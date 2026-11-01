-- Prove2me | Theorems.Thm_OLPDual_proposition_1
-- name    : OLPDual.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T09:22:14.11176+00:00
-- url     : https://prove2.me/theorems/79725727-8fb8-4e00-af06-6975576d6fba
-- title:
--   Proposition 1, p.9 — (3) and (5) share optimal solutions, $f_n$ and $f$ are convex, $d^\top p_n^*\le\bar r$, $d^\top p^*\le\bar r$
-- statement:
--   Under Assumption 1, with $b=nd$:
--
--   1. The optimal solution set of the dual LP (3) is that of problem (5), in the following sense: $(p,y)$ is optimal for (3) if and only if $p$ is optimal for (5) and $y_j=(r_j-a_j^\top p)^+$ for every $j$.
--   2. Both $f_n$ and $f$ are convex.
--   3. Every optimal solution $p_n^*$ of (6) and every optimal solution $p^*$ of (7) satisfy
--
--   $$
--   d^\top p_n^*\le\bar r,\qquad d^\top p^*\le\bar r,
--   $$
--
--   the first with probability 1 over the sample.
--
--   Since $d_i>\underline d>0$, this places both optima in the bounded region $\Omega_p$, which is where the assumptions of the paper are imposed.
--
--   Differences from the source:
--   - reading: the optimal solution set of (5) is identical to that of (3) → (p, y) is optimal for (3) iff p is optimal for (5) and y_j = (r_j − a_jᵀp)⁺; reason: (5) has no variable y; the proof on p.31 substitutes exactly this y
--   - generalization: all of Proposition 1 with probability 1 → (a) and convexity of f_n for every sample; (c) for f_n almost surely; reason: a statement for every sample implies the almost sure one
--   - generalization: f_n and f convex → ConvexOn on the whole of ℝ^m; reason: restricting to p ≥ 0 gives convexity on the feasible set
--   - generalization: Assumption 1 (d), n > m → n ≥ 1; reason: n > m ≥ 1 implies n ≥ 1 and the result does not use n > m
--   - encoding: u = (r, a) → u = (a, r); reason: order of the pair only; same law
-- source:
--   Li–Ye, Online Linear Programming: Dual Convergence, New Algorithms, and Regret Bounds, arXiv:1909.05499v5 (19 Apr 2021), Proposition 1, p.9; proof pp.31

import Mathlib
import Definitions.Def_OLPDual_Model
import Definitions.Def_OLPDual_IsDualOptimal

open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

namespace OLPDual

/-- **Proposition 1**, Li–Ye, arXiv:1909.05499v5, p.9 (PDF 9). Under Assumption 1:
(a) the optimal solutions of the dual LP (3) are exactly the `(p, y)` with `p` optimal for (5) and
`y_j = (r_j − a_jᵀp)⁺`, with `b = n d`; (b) `f_n` and `f` are convex; (c) the optimal solutions
`p*_n` and `p*` satisfy `dᵀp*_n ≤ r̄` (with probability 1) and `dᵀp* ≤ r̄`.
**Formalization Note** (a) and the convexity of `f_n` hold for every sample. Convexity is on the
whole of `ℝ^m`, and `n > m` is relaxed to `n ≥ 1`. -/
theorem proposition_1 (Θ : Model) {m n : ℕ} (hn : 0 < n) (d : E m) (law : Measure (E m × ℝ))
    [IsProbabilityMeasure law] (hA1 : Assumption1 Θ d law) :
    (∀ (ω : Sample m n) (p : E m) (y : Fin n → ℝ),
      IsDualOptimal ((n : ℝ) • d) ω p y ↔
        IsOptimal (obj5 ((n : ℝ) • d) ω) p ∧
          ∀ j, y j = max ((ω j).2 - ⟪(ω j).1, p⟫) 0) ∧
    (∀ ω : Sample m n, ConvexOn ℝ Set.univ (fn d ω)) ∧
    ConvexOn ℝ Set.univ (f d law) ∧
    (∀ᵐ ω ∂(sampleLaw law n), ∀ p, IsOptimal (fn d ω) p → ⟪d, p⟫ ≤ Θ.rbar) ∧
    ∀ p, IsOptimal (f d law) p → ⟪d, p⟫ ≤ Θ.rbar := by sorry

end OLPDual
