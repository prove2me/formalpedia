-- Prove2me | Theorems.Thm_MultiwaySoS_lemma_6
-- name    : MultiwaySoS.lemma_6
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:46.742079+00:00
-- url     : https://prove2.me/theorems/99de8a7b-fb9b-4fe9-851e-8a18b9b68fee
-- title:
--   Lemma 6 and (11) — $\mathrm{OPT}(A^t)-\sum_mr_m\mathscr X^t_m=\alpha^*\cdot\sum_{m\in\mathcal M_+}\mathscr Q^t_m$ on the ball
-- statement:
--   Let $\bar\lambda$ satisfy GPG$_{\epsilon_0}$ ($\epsilon_0>0$) with basis $\mathcal M_+$, let $\alpha$ satisfy $\sum_iM_{im}\alpha_i=r_m$ for $m\in\mathcal M_+$ (that is, $\alpha=r^\top_{\mathcal M_+}M^{-1}_{\mathcal M_+}$), and run Algorithm 2 with an arg-min commit rule on any arrival sequence. Write $\mathscr Q^t_m=(\mathscr Q^t_{im})_i$. Then for every $t$:
--
--   1. identity (11):
--   $$\sum_mr_m\mathscr X^t_m=\alpha\cdot\Big(A^t-\sum_{m\in\mathcal M_+}\mathscr Q^t_m\Big);$$
--   2. Lemma 6: if $t\ge1$ and $A^t/t\in\mathcal B_{\epsilon_0,TV}(\bar\lambda)$, then
--   $$\mathrm{OPT}(A^t)-\sum_mr_m\mathscr X^t_m=\alpha\cdot\sum_{m\in\mathcal M_+}\mathscr Q^t_m .$$
--
--   This is Step 2 of the proof of Theorem 2: the virtual reward falls short of the offline optimum by the dual price of the virtual queues.
--
--   Differences from the source:
--   - reading: $m^t=\arg\min_m\{\Delta\Phi_m(\mathscr Q^{t-1}_m,I^t)\}$ with no tie-breaking rule → every commit rule that returns a minimizer, possibly depending on the time and the whole state; reason: ties are arbitrary in the paper; a statement for every such rule covers each of them
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
--   - encoding: types $[n]$ split into the intervals $\mathcal I^{\rm off},\mathcal I^{\rm on\text{-}q},\mathcal I^{\rm on\text{-}nq}$; configurations $\mathcal M$ → `Fin n` with a labelling `kind`, configurations `Fin d`, time $1$-based, queue lengths in $\mathbb Z$; reason: a renumbering of the types; same instances
--   - encoding: $r^\top_{\mathcal M_+}M^{-1}_{\mathcal M_+}$ → any $\alpha$ with $\alpha\cdot M_m=r_m$ for $m\in\mathcal M_+$; reason: under GPG this $\alpha$ exists and is unique (basis facts), so the two are the same vector
--   - reading: Definition 2 (GPG), clause 2 "with $\mathcal M_+$ as the basic activities", and clause 1 → the support of the solution is exactly $\mathcal M_+$, whose columns are linearly independent; clause 1 is not written; reason: basic activities are the non-zero components (p.4); clause 1 follows from linear independence
--   - encoding: $\mathrm{OPT}(A^t)$, the optimal value of the LP → `sSup` of the objective over the feasible set; reason: for $A^t\ge0$ the set is nonempty (discard singletons) and bounded above under GPG (weak duality), so the supremum is the LP value
--   - generalization: Lemma 6 alone → Lemma 6 together with identity (11) (p.35), $\sum_mr_m\mathscr X^t_m=\alpha\cdot(A^t-\sum_{m\in\mathcal M_+}\mathscr Q^t_m)$, for every $t$ and every path; reason: (11) holds with no ball hypothesis and is the step Lemma 6 rests on; dropping the first conjunct leaves the printed lemma
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, Lemma 6, p.23; identity (11), p.35

import Mathlib
import Definitions.Def_MultiwaySoS_Algorithm

namespace MultiwaySoS

/-- Lemma 6 (arXiv:2112.04622v3, p.23) and identity (11), p.35.

Let `λ̄` satisfy `GPG_{ϵ₀}` (`ϵ₀ > 0`) with basis `B = M₊`, let `α` be the solution of
`α·M_m = r_m` (`m ∈ M₊`), i.e. `α = r^⊤_{M₊} M^{−1}_{M₊}`, and run Algorithm 2 with an arg-min commit
rule on any arrival sequence. Then for every `t`:
1. (11) `∑_m r_m 𝒳^t_m = α·(A^t − ∑_{m ∈ M₊} 𝒬^t_m)`;
2. (Lemma 6) if `t ≥ 1` and `A^t/t ∈ B_{ϵ₀,TV}(λ̄)`, then
   `OPT(A^t) − ∑_m r_m 𝒳^t_m = α·∑_{m ∈ M₊} 𝒬^t_m`.

**Formalization Note.** `𝒬^t_m ∈ ℝⁿ` is the column `(𝒬^t_im)_i`; `A^t/t` is automatically a
distribution for `t ≥ 1`, so the ball condition is the TV bound. -/
theorem lemma_6 {n d : ℕ} (I : Instance n d) (B : Finset (Fin d)) (σ : Fin d → List (Fin n))
    (hσ : IsCyclicOrder I σ) (lamBar : Fin n → ℝ) (ε₀ : ℝ) (xStar : Fin d → ℝ)
    (hG : IsGPG I lamBar ε₀ xStar B) (hε : 0 < ε₀) (cap : Fin n → ℝ)
    (pick : ℕ → State n d → Fin n → Fin d) (hpick : IsArgminRule I B σ pick) (arr : ℕ → Fin n)
    (α : Fin n → ℝ) (hα : ∀ m ∈ B, ∑ i, I.M i m * α i = I.r m) (t : ℕ) :
    let s := run I cap pick arr t
    virtualReward I cap pick arr t =
        ∑ i, α i * (arrCount arr t i - ∑ m ∈ B, (s.Qv I i m : ℝ)) ∧
      (1 ≤ t → tvDist lamBar (fun i => arrCount arr t i / t) ≤ ε₀ →
        OPT I (arrCount arr t) - virtualReward I cap pick arr t =
          ∑ i, α i * ∑ m ∈ B, (s.Qv I i m : ℝ)) := by sorry

end MultiwaySoS
