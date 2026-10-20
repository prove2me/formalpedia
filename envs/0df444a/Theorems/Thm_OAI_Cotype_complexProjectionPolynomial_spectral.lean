-- Prove2me | Theorems.Thm_OAI_Cotype_complexProjectionPolynomial_spectral
-- name    : OAI.Cotype.complexProjectionPolynomial_spectral
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T19:59:18.372821+00:00
-- url     : https://prove2.me/theorems/eec3c3dd-99d4-45c5-922a-0b44b136eaa6
-- title:
--   Spectral form of the complexified projection polynomial
-- statement:
--   These notions belong to a proof that a real Banach space $X$ with the approximation property is K-convex (the Rademacher projection is bounded on $L_2(\{\pm1\}^n;X)$ uniformly in $n$) if and only if $X$ and its dual $X^*$ both have finite cotype. The converse direction shows that such $X$ has nontrivial type, i.e. does not contain $\ell_1^n$ uniformly, and then derives K-convexity from a power-gap estimate for commuting coordinate projections. Let $Y$ be a real normed space and $P_1,\dots,P_m$ operators on $Y$. Let $\tilde P_i$ be their lifts to the complexified bidual $\mathcal Y=\mathcal L_{\mathbb R}(Y^*,\mathbb C)$. For $\varepsilon\in\{0,1\}^m$ let $\Pi_\varepsilon$ be the lift of the pattern product with factor $1-P_i$ where $\varepsilon_i=1$ and $P_i$ where $\varepsilon_i=0$, and let $|\varepsilon|$ be the number of ones. Then for $z\in\mathbb C$,
--   $$
--   \prod_{i=1}^m\bigl(\tilde P_i+z(1-\tilde P_i)\bigr)=\sum_{\varepsilon}z^{|\varepsilon|}\,\Pi_\varepsilon .
--   $$
--
--   So the projection polynomial is a polynomial in $z$ whose coefficients are the spectral pattern projections.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/Cotype/ComplexProjectionSpectrum.lean#L88-L104

import Mathlib
import Definitions.Def_Cotype
import Definitions.Def_OAI_Analysis_Cotype_ComplexDualLift
import Definitions.Def_OAI_Analysis_Cotype_Cube
import Definitions.Def_OAI_Analysis_Cotype_Target
import Definitions.Def_OAI_Analysis_Cotype_Moments
import Definitions.Def_OAI_Analysis_Cotype_Fourier
import Definitions.Def_OAI_Analysis_Cotype_ScalarWalsh
import Definitions.Def_OAI_Analysis_Cotype_VectorWalsh
import Definitions.Def_OAI_Analysis_Cotype_WalshNorm
import Definitions.Def_OAI_Analysis_Cotype_WalshCoordinates
import Definitions.Def_OAI_Analysis_Cotype_WalshDuality
import Definitions.Def_OAI_Analysis_Cotype_CubeNoise
import Definitions.Def_OAI_Analysis_Cotype_ProjectionProducts
import Definitions.Def_OAI_Analysis_Cotype_UniformL1
import Definitions.Def_OAI_Analysis_Cotype_BConvexity
import Definitions.Def_OAI_Analysis_Cotype_ProjectionAverages
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroup
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSemigroupBasics
import Definitions.Def_OAI_Analysis_Cotype_ProjectionSpectrum
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionPolynomial
import Definitions.Def_OAI_Analysis_Cotype_ComplexProjectionSpectrum

open OAI OAI.Cotype
open scoped BigOperators
variable {Z : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z]
variable {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem OAI.Cotype.complexProjectionPolynomial_spectral {m : ℕ} (P : Fin m → Y →L[ℝ] Y) (z : ℂ) :
    complexProjectionPolynomial P z = complexSpectralEval P (fun ε => z^(projectionDegree ε)) := by sorry
