-- Prove2me | Theorems.Thm_MultiwaySoS_virtual_queue_zero_entry
-- name    : MultiwaySoS.virtual_queue_zero_entry
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T03:18:40.365769+00:00
-- url     : https://prove2.me/theorems/808db9c1-c98c-408a-8a11-0057f851737b
-- title:
--   pp.19–20 and p.24 (corrected: $\sqrt n\sqrt\Phi$ in place of $\Phi$) — every configuration of $\mathcal M_+$ has a zero virtual queue, hence $|\mathscr Q^t_{im}|\le\sqrt n\sqrt{\Phi(\mathscr Q^t)}$
-- statement:
--   Run Algorithm 2 with an arg-min commit rule on any arrival sequence, with cyclic orders $\sigma_m$ and a basis $\mathcal M_+$ such that every resource type lies in some configuration of $\mathcal M_+$. Then at every time $t$ and for every $m\in\mathcal M_+$:
--
--   1. if $\mathcal I(m)\neq\emptyset$, some $i\in\mathcal I(m)$ has $\mathscr Q^t_{im}=0$;
--   2. if $j\in\mathcal I(m)$ is online-nonqueueable, $\mathscr Q^t_{jm}=0$;
--   3. if $m$ has no online-nonqueueable type, $\mathscr Q^t_{im}\ge0$ for all $i$;
--   4. for every $i\in\mathcal I(m)$,
--   $$|\mathscr Q^t_{im}|\le\sqrt n\,\sqrt{\Phi(\mathscr Q^t)} .$$
--
--   The bound 4 is how the proof of Theorem 2 controls the virtual queues by the potential.
--
--   Differences from the source:
--   - generalization: a run of Algorithm 2 under the hypotheses of Theorem 2 (GPG) → any arrival sequence and any basis $\mathcal M_+$ such that every type lies in some configuration of $\mathcal M_+$; reason: GPG implies this covering property (the optimal solutions with support $\mathcal M_+$ reproduce every distribution of the ball); the statement specializes to the paper\'s runs
--   - reading: $m^t=\arg\min_m\{\Delta\Phi_m(\mathscr Q^{t-1}_m,I^t)\}$ with no tie-breaking rule → every commit rule that returns a minimizer, possibly depending on the time and the whole state; reason: ties are arbitrary in the paper; a statement for every such rule covers each of them
--   - reading: matching matrix $M\in\mathbb N^{n\times d}$, with an extension to general $M_{im}$ mentioned (§4, p.15) → $M_{im}\in\{0,1\}$, stored as the sets $\mathcal I(m)$; reason: §4 says "to keep exposition clear in this paper we focus on $M_{im}\in\{0,1\}$"; the potential (5) and Algorithm 2 are defined only for this case
--   - encoding: types $[n]$ split into the intervals $\mathcal I^{\rm off},\mathcal I^{\rm on\text{-}q},\mathcal I^{\rm on\text{-}nq}$; configurations $\mathcal M$ → `Fin n` with a labelling `kind`, configurations `Fin d`, time $1$-based, queue lengths in $\mathbb Z$; reason: a renumbering of the types; same instances
--   - correction: "$\mathbb E[\mathscr Q^t_{im}]\le\mathbb E[\Phi^t]\le\mathbb E[\Psi^t]$" (p.24) → $|\mathscr Q^t_{im}|\le\sqrt n\sqrt{\Phi(\mathscr Q^t)}$ pathwise (hence $\le\sqrt n\,\Psi^t$); reason: $\Phi\le\Psi=\sqrt{\Phi+\Xi}$ fails as soon as $\Phi\ge2$ with $\Xi=0$, and the factor $\sqrt n$ cannot be dropped: the ramp $0,1,2,3,2,1$ around a $6$-cycle has largest entry $3>\sqrt6=\sqrt{\Phi}$; the corrected form is what the proof needs
--   - reading: "For every configuration" → $m\in\mathcal M_+$ with $\mathcal I(m)\ne\emptyset$; reason: the queues exist only for $\mathcal M_+$ (p.19); an empty configuration has no entry to be $0$, and GPG excludes one from $\mathcal M_+$ (a zero column is not independent)
--   - generalization: the quoted sentences → in addition, all $\mathscr Q^t_{im}\ge0$ for a configuration without an online-nonqueueable type; reason: p.19 lists only configurations with such a type as having negative virtual queues; dropping the clause leaves the quoted claim
-- source:
--   Gupta, Greedy Algorithm for Multiway Matching with Bounded Regret, arXiv:2112.04622v3, pp.19–20, "For every configuration one of the virtual queue lengths is always 0"; proof of Theorem 2, p.24, "E[𝒬^t_im] ≤ E[Φ^t] ≤ E[Ψ^t]"

import Mathlib
import Definitions.Def_MultiwaySoS_Algorithm

namespace MultiwaySoS

/-- Zero-entry invariant of the virtual queues (arXiv:2112.04622v3, pp.19–20: "For every
configuration one of the virtual queue lengths is always 0. In the case of a configuration with a
resource in I^on-nq the virtual queue length of this resource is 0. For the other configurations,
some virtual queue length must be 0 otherwise a virtual match would be completed until this was
the case."), with its consequence used in the proof of Theorem 2 (p.24, "E[𝒬^t_im] ≤ E[Φ^t]").

For every run of Algorithm 2 with an arg-min commit rule, when every type lies in some
configuration of `B = M₊`, at every time `t` and for every `m ∈ M₊`:
1. if `I(m) ≠ ∅`, some `𝒬^t_im` with `i ∈ I(m)` is `0`;
2. the virtual queue of an online-nonqueueable `j ∈ I(m)` is `0`;
3. if `m` has no online-nonqueueable type, all `𝒬^t_im ≥ 0`;
4. `|𝒬^t_im| ≤ √n · √Φ(𝒬^t)` for every `i ∈ I(m)`. -/
theorem virtual_queue_zero_entry {n d : ℕ} (I : Instance n d) (B : Finset (Fin d))
    (σ : Fin d → List (Fin n)) (hσ : IsCyclicOrder I σ) (cap : Fin n → ℝ)
    (pick : ℕ → State n d → Fin n → Fin d) (hpick : IsArgminRule I B σ pick)
    (hcover : ∀ i, ∃ m ∈ B, i ∈ I.conf m) (arr : ℕ → Fin n) (t : ℕ) (m : Fin d) (hm : m ∈ B) :
    let s := run I cap pick arr t
    ((I.conf m).Nonempty → ∃ i ∈ I.conf m, s.Qv I i m = 0) ∧
      (∀ j ∈ I.conf m, I.kind j = Kind.onNQ → s.Qv I j m = 0) ∧
      ((∀ j ∈ I.conf m, I.kind j ≠ Kind.onNQ) → ∀ i, 0 ≤ s.Qv I i m) ∧
      ∀ i ∈ I.conf m, |(s.Qv I i m : ℝ)| ≤
        Real.sqrt n * Real.sqrt ((Phi B σ (fun j m' => s.Qv I j m') : ℤ) : ℝ) := by sorry

end MultiwaySoS
