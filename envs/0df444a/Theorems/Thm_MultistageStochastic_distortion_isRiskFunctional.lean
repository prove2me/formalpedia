-- Prove2me | Theorems.Thm_MultistageStochastic_distortion_isRiskFunctional
-- name    : MultistageStochastic.distortion_isRiskFunctional
-- status  : Open
-- author  : @naimengye
-- created : 2026-09-23T20:23:06.788835+00:00
-- url     : https://prove2.me/theorems/5dac002a-919b-4556-be8f-78d95e4c934f
-- title:
--   Section 3.2 — a distortion risk functional is a risk functional
-- statement:
--   Let $(\Omega,\mathcal F,P)$ be a probability space and $\sigma$ a distortion function: nonnegative
--   and nondecreasing on $[0,1)$ with $\int_0^1\sigma=1$. Then the distortion risk functional
--
--   $$
--   \mathcal R_\sigma(Y)=\int_0^1\sigma(u)\,\mathsf{V@R}_u(Y)\,du
--   $$
--
--   is a **risk functional** in the sense of Definition 3.2: on $L^\infty$ it is monotone (M),
--   convex (C), translation equivariant (T) and positively homogeneous (H).
--
--   The source proves each axiom in one clause: (T) because $\sigma$ integrates to one, (M) because
--   $\sigma\ge 0$ and the quantile function is monotone in $Y$, (H) because the Value-at-Risk is
--   positively homogeneous, and (C) from $\sigma$ being nondecreasing, which is the one nontrivial
--   step — the Value-at-Risk itself is not convex (mission II), and it is the weighting by a
--   nondecreasing density that restores convexity.
--
--   **Formalization Note** The risk-functional predicate is mission II's `IsRiskFunctional`, whose
--   four axioms are quantified over $L^\infty$ arguments. The theorem asserts all four for the
--   functional $Y\mapsto\mathcal R_\sigma(Y)$ as defined on every $Y:\Omega\to\mathbb R$; its values
--   off $L^\infty$ do not enter.
-- source:
--   Georg Ch. Pflug and Alois Pichler, Multistage Stochastic Optimization, Springer 2014, https://doi.org/10.1007/978-3-319-08843-3 — Section 3.2, printed p. 99 (PDF p. 112), after Definition 3.6: "The distortion risk functional is a risk functional. Indeed, translation equivariance (T) holds because ∫_0^1 σ(u) du = 1, monotonicity (M) is ensured by the assumption σ ≥ 0, positive homogeneity (H) is automatically satisfied for functionals with representation (3.7), since V@R is positively homogeneous and convexity (C) follows by assuming that σ is nondecreasing."

import Definitions.Def_MultistageStochastic_RiskFunctional
import Definitions.Def_MultistageStochastic_Distortion
open MeasureTheory
open scoped ENNReal

namespace MultistageStochastic
theorem distortion_isRiskFunctional {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (σ : ℝ → ℝ) (hσ : IsDistortionFunction σ) :
    IsRiskFunctional P (distortionFunctional P σ) := by sorry
end MultistageStochastic
