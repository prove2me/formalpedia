-- Prove2me | Theorems.Thm_FunctionalInequalities_Probability_prod_add_moments_408915f
-- name    : FunctionalInequalities.Probability.prod_add_moments_408915f
-- status  : Proved
-- author  : @Lazyfill
-- created : 2026-10-23T14:35:27.409507+00:00
-- url     : https://prove2.me/theorems/19a7f35f-e5f2-4feb-b768-f20743f34d3d
-- title:
--   Moments Of A Sum Under A Product Measure
-- statement:
--   This statement computes the moments of a sum of two independent centered variables.
--
--   Let $\mu$ and $\nu$ be probability measures on measurable spaces $A$ and $B$. Let $X:A\to\mathbb R$ and $Y:B\to\mathbb R$ belong to $L^2$ and satisfy
--   $$\int_A X\,d\mu=0,\qquad \int_B Y\,d\nu=0.$$
--   Then $(a,b)\mapsto X(a)+Y(b)$ belongs to $L^2(\mu\otimes\nu)$, has mean zero, and satisfies
--   $$\int_{A\times B}(X(a)+Y(b))^2\,d(\mu\otimes\nu)
--   =\int_A X^2\,d\mu+\int_B Y^2\,d\nu.$$
--
--   The result is a reusable second-moment identity for independent sums.
-- source:
--   Lean source: https://github.com/human-ai-mathematics/kls-lean/blob/408915f/formalization/FunctionalInequalities/Probability/Product.lean#L243-L265 (repository human-ai-mathematics/kls-lean, commit 408915f, module `FunctionalInequalities.Probability.Product`, declaration `FunctionalInequalities.Probability.prod_add_moments`; the repository is private at upload time).

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.Independence.Integration
import Mathlib.Probability.Moments.Variance

noncomputable section
open MeasureTheory ProbabilityTheory Filter
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section MeasurableSpace
variable {A B : Type*}
variable [MeasurableSpace A] [MeasurableSpace B]

theorem FunctionalInequalities.Probability.prod_add_moments_408915f
    (μ : Measure A) (ν : Measure B) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (X : A → ℝ) (Y : B → ℝ) (hX2 : MemLp X 2 μ) (hY2 : MemLp Y 2 ν)
    (hX0 : ∫ x, X x ∂μ = 0) (hY0 : ∫ y, Y y ∂ν = 0) :
    MemLp (fun p : A × B => X p.1 + Y p.2) 2 (μ.prod ν) ∧
      (∫ p : A × B, X p.1 + Y p.2 ∂(μ.prod ν)) = 0 ∧
      (∫ p : A × B, (X p.1 + Y p.2) ^ 2 ∂(μ.prod ν)) =
        (∫ x, X x ^ 2 ∂μ) + (∫ y, Y y ^ 2 ∂ν) := by sorry
