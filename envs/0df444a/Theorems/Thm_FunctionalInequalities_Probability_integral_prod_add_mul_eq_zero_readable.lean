-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_integral_prod_add_mul_eq_zero_readable
-- name    : FunctionalInequalities.Probability.integral_prod_add_mul_eq_zero_readable
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-26T13:18:02.339005+00:00
-- url     : https://prove2.me/theorems/06ead519-d490-40d0-8b01-8870b5c2236a
-- title:
--   Orthogonality After Adding an Independent Centered Observable
-- statement:
--   This lemma gives a vanishing mixed moment on a binary product probability space.
--
--   Let $A,B$ be measurable spaces with probability measures $\mu,\nu$, respectively. Let $X,Z:A\to\mathbb R$ and $Y:B\to\mathbb R$. Assume:
--   1. $X,Z\in L^2(\mu)$ and $Y\in L^2(\nu)$ (`MemLp`).
--   2. $\int XZ\,d\mu=0$.
--   3. $\int Y\,d\nu=0$.
--
--   For the product measure $\mu\otimes\nu$ (`Measure.prod`),
--   $$
--   (x,y)\mapsto(X(x)+Y(y))Z(x)\in L^1(\mu\otimes\nu),\qquad
--   \int (X(x)+Y(y))Z(x)\,d(\mu\otimes\nu)(x,y)=0.
--   $$
--
--   This is a reusable mixed-moment identity; neither $X$ nor $Z$ is required to be centered.
--
--   **Original Lean declaration header**
--
--   Within namespace `FunctionalInequalities.Probability`. Shown in its original module context. Proof omitted.
--
--   ```lean
--   theorem integral_prod_add_mul_eq_zero
--       (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
--       (X Z : A → ℝ) (Y : B → ℝ)
--       (hX2 : MemLp X 2 μ) (hZ2 : MemLp Z 2 μ) (hY2 : MemLp Y 2 ν)
--       (hXZ0 : ∫ x, X x * Z x ∂μ = 0) (hY0 : ∫ y, Y y ∂ν = 0) :
--       Integrable (fun p : A × B => (X p.1 + Y p.2) * Z p.1) (μ.prod ν) ∧
--         (∫ p : A × B, (X p.1 + Y p.2) * Z p.1 ∂(μ.prod ν)) = 0
--   ```
--
--   **Module navigation**
--
--   Module: [`Probability/Product`](https://prove2.me/theorems/dfc6100e-7e58-40e2-978d-c3597731ccef).
--
--   Previous: [`prod_add_moments`](https://prove2.me/theorems/f5585b5d-7720-411a-8489-0d9bfb7bd7e5).
--
--   [Source excerpt, lines 268–274](https://github.com/human-ai-mathematics/kls-lean/blob/408915fd28eb892a7093fa5df6f6c2699e9de144/formalization/FunctionalInequalities/Probability/Product.lean#L268-L274) · Frozen source `408915f`.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Product.lean#L267-L291 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Product`, declaration `FunctionalInequalities.Probability.integral_prod_add_mul_eq_zero`; the repository is private at upload time).

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_Product

open MeasureTheory ProbabilityTheory Filter
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]

theorem FunctionalInequalities.Probability.integral_prod_add_mul_eq_zero_readable
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X Z : A → ℝ) (Y : B → ℝ)
    (hX2 : MemLp X 2 μ) (hZ2 : MemLp Z 2 μ) (hY2 : MemLp Y 2 ν)
    (hXZ0 : ∫ x, X x * Z x ∂μ = 0) (hY0 : ∫ y, Y y ∂ν = 0) :
    Integrable (fun p : A × B => (X p.1 + Y p.2) * Z p.1) (μ.prod ν) ∧
      (∫ p : A × B, (X p.1 + Y p.2) * Z p.1 ∂(μ.prod ν)) = 0 := by sorry
