-- Prove2me | Theorems.Thm_OAI_EuclideanSteinitz_GaussianCorrelation_linear_image_finite_correlation
-- name    : OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:18:50.003443+00:00
-- url     : https://prove2.me/theorems/8f05a3ca-84b2-4d84-83d6-fee58fd3dd48
-- title:
--   Royen's Gaussian correlation inequality for finitely many closed symmetric convex sets under a linear image of the standard Gaussian measure
-- statement:
--   Let $E$ be a finite-dimensional real inner product space (`NormedAddCommGroup E`, `InnerProductSpace ℝ E`, `FiniteDimensional ℝ E`) with its Borel σ-algebra (`MeasurableSpace E`, `BorelSpace E`), and let $\gamma$ be the standard Gaussian measure on $E$ (Mathlib's `stdGaussian E`). Let $F$ be a real normed space (`NormedAddCommGroup F`, `NormedSpace ℝ F`) with its Borel σ-algebra (`MeasurableSpace F`, `BorelSpace F`), let $A : E \to F$ be a continuous linear map (`A : E →L[ℝ] F`), and write $\nu = A_*\gamma$ (`(stdGaussian E).map A`). Let $\iota$ be any type, $s$ a finite set of indices (`s : Finset ι`), and $K_i \subseteq F$ ($i \in \iota$) sets such that for every $i \in s$:
--   - $K_i$ is closed (`IsClosed (K i)`),
--   - $K_i$ is convex (`Convex ℝ (K i)`), and
--   - $K_i$ is symmetric about the origin: $-x \in K_i$ for every $x \in K_i$.
--
--   Then
--   $$\prod_{i \in s} \nu(K_i) \;\le\; \nu\Bigl(\bigcap_{i \in s} K_i\Bigr).$$
--   In Lean the measures are real numbers (`Measure.real`); for $s = \emptyset$ the left side is $1$ and the right side is $\nu(F) = 1$.
--
--   This is the Gaussian correlation inequality (T. Royen, 2014) iterated over finitely many sets, for linear images of a finite-dimensional standard Gaussian measure.
--
--   Lean: `OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation`, OpenAI's lemma of that name (in `lean/OAI/Analysis/Steinitz/Correlation.lean`). The statement uses only Mathlib's definitions and imports no definitions bundle.
-- source:
--   T. Royen, A simple proof of the Gaussian correlation conjecture extended to some multivariate gamma distributions, Far East J. Theor. Stat. 48 (2014), 139–145 (the theorem); proof and Lean code: OpenAI, The Euclidean Steinitz–Bergström theorem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 097; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Steinitz/Correlation.lean (declaration OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation)

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

lemma linear_image_finite_correlation {ι : Type*} (A : E →L[ℝ] F)
    (s : Finset ι) (K : ι → Set F)
    (hK : ∀ i ∈ s, IsClosed (K i)) (hcK : ∀ i ∈ s, Convex ℝ (K i))
    (hsK : ∀ i ∈ s, ∀ x ∈ K i, -x ∈ K i) :
    ∏ i ∈ s, ((stdGaussian E).map A).real (K i) ≤
      ((stdGaussian E).map A).real (⋂ i ∈ s, K i) := by
  sorry

end EuclideanSteinitz.GaussianCorrelation

end

end OAI
end
