-- Prove2me | Theorems.Thm_HierADA_proposition_3_4
-- name    : HierADA.proposition_3_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-08T18:07:48.266126+00:00
-- url     : https://prove2.me/theorems/704bba96-d745-4228-ada5-490a10cc7484
-- title:
--   Proposition 3.4 — progress and correction bounds
-- statement:
--   Let $\alpha,\xi\in(0,\frac1{10})$ with the parameters $p,\tau,\varepsilon_j,B_j$ of Section 3.2, and any block sizes $n_j$. Let the sample blocks and the noise lie in the good event $E$, and fix reference vectors $u_j\in W_j$ for the learned blocks $j<p$ with $|\langle u_j,f_t(S_j)\rangle-Pf_t|\le\tau/64$ for every query of the auxiliary execution and $R_j(u_j)\le\varepsilon_j^2$. Along the auxiliary execution:
--
--   1. every correction on edge $j$ decreases the potential $\Psi$ by at least $4^{j-1}\tau^2/16$;
--   2. every prefix of the execution satisfies
--   $$
--   \sum_{j=1}^{p-1}4^{j-1}T_j\le\frac{16}{\tau^2},
--   $$
--   where $T_j$ counts the corrections on edge $j$ in the prefix (Equation (12));
--   3. $T_j\le\frac{16}{4^{j-1}\tau^2}$ for every edge $j$;
--   4. the total number of corrections is at most $16/\tau^2$;
--   5. no correction limit is reached: $T_j<B_j$;
--   6. block $1$ receives at most $16/\tau^2$ weight updates, and each block $2\le j<p$ at most $\frac{80}{4^{j-1}\tau^2}$.
--
--   The bounds hold deterministically on $E$; together with the privacy theorem they show that the auxiliary and the original mechanism agree with high probability.
--
--   **Formalization Note** The scores before the $s$-th correction are those recorded after the previous correction (initially $0$). A learned block $j\ge2$ is updated by the corrections on its two incident edges $j-1$ and $j$.
--
--   Differences from the source:
--   - reading: “Let α, δ < 1/10 be the accuracy and failure parameters” (p.18) → 0 < α < 1/10 and 0 < ξ < 1/10; reason: δ there is the failure parameter, called ξ in the rest of Section 3; δ is later the privacy slack τξ/(4096(p+1))
--   - reading: Algorithm 2 scans while j ≤ p and updates G_{j+1} if j + 1 ≤ p → only the edges j ∈ [1, p) are scanned and the anchor's score is never updated; reason: there is no block p + 1, the anchor's weights stay uniform (p.13), and the proof of Proposition 3.4 says that on the last edge only block p − 1 is updated (p.22)
--   - encoding: “Conditioned on the event E, every correction …” → for every (S, z) in the good event and every choice of reference vectors satisfying Proposition 3.2 (1); reason: the argument is deterministic (p.19: “The argument below is deterministic”)
--   - generalization: the block sizes n_j and noise scale b chosen in Section 3.3 → arbitrary block sizes n_j; the noise is a fixed realization; reason: the deterministic argument uses neither; the paper's choice is a special case
--   - encoding: T_j for every prefix, the number of weight updates of a block → counts of corrections on each edge in the first s recorded corrections; block j ≥ 1 counts edges j − 1 and j, block 0 counts edge 0; reason: same quantities
--   - encoding: blocks and edges numbered from 1, multipliers 4^{j−1} → 0-based Fin p indices, multipliers 4^j; reason: renumbering only
-- source:
--   Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou, Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams, preprint (version of 2026-11-03, sha256 f220ae51…), Proposition 3.4, p.21, Equation (12)

import Mathlib
import Definitions.Def_IsRandomnessNecessaryADA_Plain_Protocol
import Definitions.Def_HierADA_params__e3298e
import Definitions.Def_HierADA_auxRun
import Definitions.Def_HierADA_goodEvent
import Definitions.Def_HierADA_potential

set_option autoImplicit false

open IsRandomnessNecessaryADA.Plain

namespace HierADA

/-- **Proposition 3.4 (Progress and correction bounds)** — Gribelyuk–Lin–Lyu–Majid–Woodruff–Yu–Zhou,
*Adaptive Data Analysis and Adversarial Robustness on Insertion-Deletion Streams*, preprint (version
of 2026-11-03, sha256 f220ae51…), Proposition 3.4, p.21, Equation (12).

Let `α, ξ ∈ (0, 1/10)` with the parameters of Section 3.2, let `(S, z)` lie in the good event `E`,
and fix reference vectors `u_j ∈ W_j` (`j < p`) as in Proposition 3.2 (1). Along the auxiliary
execution:
1. every correction on edge `j` decreases `Ψ` by at least `4^{j-1} τ²/16`;
2. every prefix of the execution satisfies `∑_{j=1}^{p-1} 4^{j-1} T_j ≤ 16/τ²`;
3. `T_j ≤ 16/(4^{j-1} τ²)` for every edge `j`;
4. the total number of corrections is at most `16/τ²`;
5. no correction limit is reached: `T_j < B_j`;
6. block 1 receives at most `16/τ²` weight updates, and each block `2 ≤ j < p` at most
   `80/(4^{j-1} τ²)`.

**Formalization Note.** 0-based indices: Lean's edge/block `j` is the paper's `j + 1`, so `4^{j-1}`
is `4^j`. The corrections are `R.corrections`, each recorded with its edge and the score vectors after
it; the scores before the `s`-th correction are those after the `(s−1)`-th (initially `0`). `T_j` of a
prefix of `s` corrections is the number of them on edge `j`; `R.T` are the final counts. Block `0` is
updated by the corrections on edge `0`, and a learned block `j ≥ 1` by those on edges `j − 1` and `j`.
`ξ` enters only through the standing assumption. -/
theorem proposition_3_4 {X : Type} [Fintype X] (α ξ : ℝ) (hα0 : 0 < α) (hα : α < 1 / 10)
    (hξ0 : 0 < ξ) (hξ : ξ < 1 / 10) (k : ℕ) (P : PMF X) (A : Analyst X)
    (n : Fin (params α ξ k).p → ℕ) (S : (j : Fin (params α ξ k).p) → Fin (n j) → X) (z : Noise)
    (hE : (S, z) ∈ goodEvent (params α ξ k) k P n A)
    (u : (j : Fin (params α ξ k).p) → Fin (n j) → ℝ)
    (hu : ∀ j : Fin (params α ξ k).p, j.val + 1 < (params α ξ k).p →
      u j ∈ NondualOpt.cappedSimplex (n j) 8 ∧
      (∀ f ∈ (auxRun (params α ξ k) n S z A k).queries,
        |∑ i, u j i * (f (S j i) : ℝ) - populationMean P f| ≤ (params α ξ k).τ / 64) ∧
      penalty (n j) (u j) ≤ (params α ξ k).ε j ^ 2) :
    let prm := params α ξ k
    let R := auxRun prm n S z A k
    let before : ℕ → ((j : Fin prm.p) → Fin (n j) → ℝ) := fun s =>
      ((R.corrections.take s).getLast?.map Prod.snd).getD fun _ _ => 0
    let cnt : ℕ → ℕ → ℕ := fun s j => ((R.corrections.take s).filter fun c => c.1 = j).length
    (∀ (s : ℕ) (hs : s < R.corrections.length),
      potential prm n u (before s) - potential prm n u (R.corrections[s]'hs).2 ≥
        (4 : ℝ) ^ (R.corrections[s]'hs).1 * prm.τ ^ 2 / 16) ∧
    (∀ s ≤ R.corrections.length,
      ∑ j ∈ Finset.range (prm.p - 1), (4 : ℝ) ^ j * (cnt s j : ℝ) ≤ 16 / prm.τ ^ 2) ∧
    (∀ j : Fin prm.p, j.val + 1 < prm.p → (R.T j : ℝ) ≤ 16 / ((4 : ℝ) ^ j.val * prm.τ ^ 2)) ∧
    ((R.corrections.length : ℝ) ≤ 16 / prm.τ ^ 2) ∧
    (∀ j : Fin prm.p, j.val + 1 < prm.p → R.T j < prm.B j) ∧
    ((cnt R.corrections.length 0 : ℝ) ≤ 16 / prm.τ ^ 2) ∧
    (∀ j : Fin prm.p, 1 ≤ j.val → j.val + 1 < prm.p →
      ((cnt R.corrections.length (j.val - 1) + cnt R.corrections.length j.val : ℕ) : ℝ) ≤
        80 / ((4 : ℝ) ^ j.val * prm.τ ^ 2)) := by sorry

end HierADA
