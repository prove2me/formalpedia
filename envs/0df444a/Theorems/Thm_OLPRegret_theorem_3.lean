-- Prove2me | Theorems.Thm_OLPRegret_theorem_3
-- name    : OLPRegret.theorem_3
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T14:04:37.283995+00:00
-- url     : https://prove2.me/theorems/21bae2b4-8c10-4754-86b7-f9a8671d9651
-- title:
--   Theorem 3 — the expected regret of the optimal online policy is $\Omega(\log n)$ (corrected: $m\ge1$)
-- statement:
--   Let $m\ge1$, let $\mu$ be a law on $\mathbb R\times\mathbb R^m$ and $\beta\in\mathbb R^m_+$, and suppose Assumptions 2–6 hold, the customers being i.i.d. from $\mu$ (Assumption 1). Then there are $c>0$ and $N$ such that for every $n\ge N$ and every non-anticipating policy of horizon $n$,
--   $$
--   \mathrm E(V_n^\beta)-\mathrm E(\text{online value})\ge c\log n,
--   $$
--   where $V_n^\beta$ is the offline integer program (16). In particular the optimal policy (14) of the online linear program with known $\mu$ has $\mathrm E(R_n)=\Omega(\log n)$.
--
--   Together with Theorem 1 this pins the regret of the known-distribution problem at $\Theta(\log n)$, extending Lueker's one-dimensional bound to $m$ resources.
--
--   **Formalization Note** The constants $c,N$ come before $n$ and before the policy.
--
--   Differences from the source:
--   - correction: $m$ unrestricted → $1\le m$; reason: at $m=0$, with $u_1\equiv1$ and $a_1\in\mathbb R^0$, Assumptions 1–6 hold vacuously and $R_n=0$ (proved in the mission's verification file)
--   - generalization: the optimal policy (14) → every measurable non-anticipating policy, with $c$ and $N$ uniform over policies; reason: the optimal policy is one of them (`OLPRegret.bellman_optimal`), so this specializes to the page
--   - encoding: $\Omega(\log n)$ as $n\to\infty$ → $\exists c>0,\exists N,\forall n\ge N$, with `Real.log`; reason: standard meaning; the base only rescales $c$
--   - encoding: periods counted backward, $t=n,\dots,1$ → the index $t$ of `Fin n` holds period $t+1$, and the stock $tb_t$ is tracked with $b_t$ recovered by division; reason: Lean convention; same instances
-- source:
--   Bray, arXiv:1912.08917v6, Theorem 3, p.21; proof §4.5, pp.30–32, and Online Appendix pp.18–26 (PDF 54–62)

import Mathlib
import Definitions.Def_OLPRegret_regret

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal Topology

namespace OLPRegret

/-- Bray, arXiv:1912.08917v6, Theorem 3, p.21: the optimal policy of the online linear program without
learning yields an expected regret that grows at no less than a `log n` asymptotic rate,
`E(Rₙ) = Ω(log n)` as `n → ∞`, when `μ` is known to the decision maker.

**Formalization Note** Stated for every non-anticipating policy, with `c` and `N` chosen before `n`
and before the policy. The optimal policy (14) is one of them (`OLPRegret.bellman_optimal`). The
benchmark is the integer program (16). `1 ≤ m` corrects the statement: at `m = 0` every assumption
holds vacuously and the regret is `0`. -/
theorem theorem_3 {m : ℕ} (hm : 1 ≤ m) (μ : Measure (Customer m)) [IsProbabilityMeasure μ] (β : E m)
    (hβ : VNonneg β) (hA : Assumptions μ β) :
    ∃ c : ℝ, 0 < c ∧ ∃ N : ℕ, ∀ n ≥ N, ∀ π : Policy m n,
      c * Real.log n ≤ regret μ β π := by sorry

end OLPRegret
