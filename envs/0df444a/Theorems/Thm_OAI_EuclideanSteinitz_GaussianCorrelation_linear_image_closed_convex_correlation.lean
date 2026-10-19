-- Prove2me | Theorems.Thm_OAI_EuclideanSteinitz_GaussianCorrelation_linear_image_closed_convex_correlation
-- name    : OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_closed_convex_correlation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:18:49.136708+00:00
-- url     : https://prove2.me/theorems/567dd9e6-607d-4244-8e9f-5d31de04748c
-- title:
--   Royen's Gaussian correlation inequality for a linear image of the standard Gaussian measure and two closed symmetric convex sets
-- statement:
--   Let $E$ be a finite-dimensional real inner product space (`NormedAddCommGroup E`, `InnerProductSpace ℝ E`, `FiniteDimensional ℝ E`) with its Borel σ-algebra (`MeasurableSpace E`, `BorelSpace E`), and let $\gamma$ be the standard Gaussian measure on $E$ (Mathlib's `stdGaussian E`). Let $F$ be a real normed space (`NormedAddCommGroup F`, `NormedSpace ℝ F`) with its Borel σ-algebra (`MeasurableSpace F`, `BorelSpace F`), and let $A : E \to F$ be a continuous linear map (`A : E →L[ℝ] F`). Write $\nu = A_*\gamma$ for the image measure (`(stdGaussian E).map A`). Let $K, L \subseteq F$ be sets that are
--   - closed (`IsClosed K`, `IsClosed L`),
--   - convex (`Convex ℝ K`, `Convex ℝ L`), and
--   - symmetric about the origin: $-x \in K$ for every $x \in K$, and $-x \in L$ for every $x \in L$.
--
--   Then
--   $$\nu(K)\,\nu(L) \;\le\; \nu(K \cap L).$$
--   In Lean the measures are real numbers (`Measure.real`).
--
--   This is the Gaussian correlation inequality (T. Royen, 2014) for centered Gaussian measures that are linear images of a finite-dimensional standard Gaussian, which includes every centered Gaussian measure on a finite-dimensional space.
--
--   Lean: `OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_closed_convex_correlation`, OpenAI's lemma of that name (in `lean/OAI/Analysis/Steinitz/Correlation.lean`). The statement uses only Mathlib's definitions and imports no definitions bundle.
-- source:
--   T. Royen, A simple proof of the Gaussian correlation conjecture extended to some multivariate gamma distributions, Far East J. Theor. Stat. 48 (2014), 139–145 (the theorem); proof and Lean code: OpenAI, The Euclidean Steinitz–Bergström theorem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 097; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Steinitz/Correlation.lean (declaration OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_closed_convex_correlation)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace EuclideanSteinitz.GaussianCorrelation
open MeasureTheory ProbabilityTheory
open scoped RealInnerProductSpace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]

lemma linear_image_closed_convex_correlation (A : E →L[ℝ] F) {K L : Set F}
    (hK : IsClosed K) (hL : IsClosed L) (hcK : Convex ℝ K) (hcL : Convex ℝ L)
    (hsK : ∀ x ∈ K, -x ∈ K) (hsL : ∀ x ∈ L, -x ∈ L) :
    ((stdGaussian E).map A).real K * ((stdGaussian E).map A).real L ≤
      ((stdGaussian E).map A).real (K ∩ L) := by
  sorry

end EuclideanSteinitz.GaussianCorrelation

end

end OAI
end
