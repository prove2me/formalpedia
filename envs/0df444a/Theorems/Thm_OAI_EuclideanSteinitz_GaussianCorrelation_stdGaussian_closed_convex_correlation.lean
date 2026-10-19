-- Prove2me | Theorems.Thm_OAI_EuclideanSteinitz_GaussianCorrelation_stdGaussian_closed_convex_correlation
-- name    : OAI.EuclideanSteinitz.GaussianCorrelation.stdGaussian_closed_convex_correlation
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-18T19:18:49.27199+00:00
-- url     : https://prove2.me/theorems/188a9364-3c82-4492-8b33-d7f333f3b043
-- title:
--   Royen's Gaussian correlation inequality for the standard Gaussian measure and two closed symmetric convex sets
-- statement:
--   Let $E$ be a finite-dimensional real inner product space (`NormedAddCommGroup E`, `InnerProductSpace ℝ E`, `FiniteDimensional ℝ E`) carrying its Borel σ-algebra (`MeasurableSpace E`, `BorelSpace E`), and let $\gamma$ be the standard Gaussian measure on $E$ (Mathlib's `stdGaussian E`: the law of $\sum_i \xi_i e_i$ for an orthonormal basis $(e_i)$ of $E$ and independent standard normal $\xi_i$). Let $K, L \subseteq E$ be sets that are
--   - closed (`IsClosed K`, `IsClosed L`),
--   - convex (`Convex ℝ K`, `Convex ℝ L`), and
--   - symmetric about the origin: $-x \in K$ for every $x \in K$, and $-x \in L$ for every $x \in L$.
--
--   Then
--   $$\gamma(K)\,\gamma(L) \;\le\; \gamma(K \cap L).$$
--   In Lean the measures are real numbers, `(stdGaussian E).real K * (stdGaussian E).real L ≤ (stdGaussian E).real (K ∩ L)`. The sets may be empty; then both sides are $0$.
--
--   This is the Gaussian correlation inequality, proved by T. Royen (2014), for the standard Gaussian measure and closed sets. Every centered Gaussian measure on a finite-dimensional space is a linear image of a standard one; the published companion statements `OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_closed_convex_correlation` and `OAI.EuclideanSteinitz.GaussianCorrelation.linear_image_finite_correlation` give that form and the form for finitely many sets.
--
--   Lean: `OAI.EuclideanSteinitz.GaussianCorrelation.stdGaussian_closed_convex_correlation`, OpenAI's lemma of that name (in `lean/OAI/Analysis/Steinitz/Correlation.lean`). The statement uses only Mathlib's definitions and imports no definitions bundle.
-- source:
--   T. Royen, A simple proof of the Gaussian correlation conjecture extended to some multivariate gamma distributions, Far East J. Theor. Stat. 48 (2014), 139–145 (the theorem); proof and Lean code: OpenAI, The Euclidean Steinitz–Bergström theorem, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 097; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/Steinitz/Correlation.lean (declaration OAI.EuclideanSteinitz.GaussianCorrelation.stdGaussian_closed_convex_correlation)

import Mathlib

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section

namespace EuclideanSteinitz.GaussianCorrelation
open Matrix MeasureTheory ProbabilityTheory _root_.Filter InnerProductSpace
open scoped NNReal RealInnerProductSpace MatrixOrder Matrix.Norms.L2Operator Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

lemma stdGaussian_closed_convex_correlation {K L : Set E}
    (hK : IsClosed K) (hL : IsClosed L) (hcK : Convex ℝ K) (hcL : Convex ℝ L)
    (hsK : ∀ x ∈ K, -x ∈ K) (hsL : ∀ x ∈ L, -x ∈ L) :
    (stdGaussian E).real K * (stdGaussian E).real L ≤ (stdGaussian E).real (K ∩ L) := by
  sorry

end EuclideanSteinitz.GaussianCorrelation

end

end OAI
end
