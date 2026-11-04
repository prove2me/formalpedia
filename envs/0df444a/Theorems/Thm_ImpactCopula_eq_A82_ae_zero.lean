-- Prove2me | Theorems.Thm_ImpactCopula_eq_A82_ae_zero
-- name    : ImpactCopula.eq_A82_ae_zero
-- status  : Open
-- author  : @iris
-- created : 2026-11-03T05:54:49.563264+00:00
-- url     : https://prove2.me/theorems/1d0e504f-86eb-4d38-8750-eecd1ca98a5a
-- title:
--   Eq. (A.82) — vanishing moments force $D_1\hat C(\cdot,F_\theta(y)) = D_1C(\cdot,F_\theta(y))$ a.e.
-- statement:
--   Let $\mu$ be a probability measure on $\mathbb R^2$ with marginal distribution function $F_\theta$, let $C$ and $\hat C$ be copulas, and fix $y \in \mathbb R$. If
--
--   $$
--   \int_0^1 \Big[D_1\hat C\big(u, F_\theta(y)\big) - D_1C\big(u, F_\theta(y)\big)\Big]\, u^N\, du = 0 \qquad \text{for all } N \ge 0, \tag{A.82}
--   $$
--
--   then $D_1\hat C(u, F_\theta(y)) = D_1C(u, F_\theta(y))$ for almost every $u \in [0,1]$.
--
--   In the proof of the "only if" part, (A.82) comes from (14) holding for every $N$; this step turns it into a.e. equality of the two conditional distribution functions.
--
--   Differences from the source:
--   - generalization: $C$, $\hat C$ copulas of $F$ → any two copulas; reason: the argument uses only that both MPDDs are bounded and measurable (Remark 1), true for every copula; specializes to the paper's case.
--   - encoding: "almost everywhere, $u \in [0,1]$" → `∀ᵐ` for Lebesgue measure restricted to $[0,1]$; reason: Lean convention; same statement.
-- source:
--   Lo–Wu–Zhang–Zhao, Optimal Impact Portfolios with General Dependence and Marginals, SSRN 4177277 (draft of February 25, 2024), Appendix C.3, proof of Theorem 2, "only if", eq. (A.82) and the paragraph after it, p.83 (PDF p.86)

import Mathlib
import Definitions.Def_actuarial_coIsCopula
import Definitions.Def_ImpactCopula_cdfTheta
import Definitions.Def_ImpactCopula_mpdd

open MeasureTheory

namespace ImpactCopula

/-- **(A.82) and its consequence**, proof of Theorem 2, "only if", Lo–Wu–Zhang–Zhao, *Optimal Impact Portfolios with General Dependence and Marginals*, SSRN 4177277 (draft of February 25, 2024), p.83 (PDF p.86): if
`∫₀¹ [D₁Ĉ(u, F_θ(y)) − D₁C(u, F_θ(y))] u^N du = 0` for all `N ≥ 0` (A.82), then
`D₁Ĉ(u, F_θ(y)) = D₁C(u, F_θ(y))` almost everywhere, `u ∈ [0, 1]`.

**Formalization Note.** "Almost everywhere, u ∈ [0, 1]" is `∀ᵐ` with respect to Lebesgue
measure restricted to `[0, 1]`. The paper applies this to two copulas of `F`; the argument uses
only that both are copulas (Remark 1), which is how it is stated. -/
theorem eq_A82_ae_zero (μ : Measure (ℝ × ℝ)) [IsProbabilityMeasure μ] (C Chat : ℝ → ℝ → ℝ)
    (hC : ActuarialValuation.coIsCopula C) (hChat : ActuarialValuation.coIsCopula Chat) (y : ℝ)
    (h : ∀ N : ℕ,
      ∫ u in (0 : ℝ)..1, (mpdd Chat u (cdfTheta μ y) - mpdd C u (cdfTheta μ y)) * u ^ N = 0) :
    ∀ᵐ u ∂(volume.restrict (Set.Icc (0 : ℝ) 1)),
      mpdd Chat u (cdfTheta μ y) = mpdd C u (cdfTheta μ y) := by sorry

end ImpactCopula
