-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_gaussianCoupling_map_noisyObservation
-- name    : OAI.SubsphereRegression.gaussianCoupling_map_noisyObservation
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:18:08.883988+00:00
-- url     : https://prove2.me/theorems/eaa20593-3491-478c-a639-058f1a062767
-- title:
--   Density of Gaussian-design observations with Gaussian label noise
-- statement:
--   Let $E$ be a finite-dimensional real inner product space of dimension $d$, with its Borel $\sigma$-algebra, and let $\gamma_E$ be the standard Gaussian measure on $E$ (its coordinates in any orthonormal basis are independent standard normal variables). For $m\ge0$ write $\lambda_m$ for Lebesgue measure on $\mathbb{R}^m$, and let $R_m=\gamma_E^{\otimes m}\otimes\lambda_m$ be the reference measure on $E^m\times\mathbb{R}^m$. Let $\nu$ be a $\sigma$-finite Borel measure on $E$ (not necessarily a probability measure), let $m\ge0$ and let $\delta\in\mathbb{R}$ with $\delta\ne0$. On $E^m\times(E\times\mathbb{R}^m)$ consider the product measure
--   $$\Gamma_{\nu,m}=\gamma_E^{\otimes m}\otimes\bigl(\nu\otimes N(0,1)^{\otimes m}\bigr)$$
--   of $m$ independent standard Gaussian rows $A_1,\dots,A_m\in E$, a parameter $t$ drawn from $\nu$, and independent standard normal noise $\xi\in\mathbb{R}^m$, and the noisy observation map $O_\delta(A,(t,\xi))=(A,y)$ with $y_j=\langle t,A_j\rangle+\delta\xi_j$. With $g_{\delta^2}(x)=(2\pi\delta^2)^{-1/2}e^{-x^2/(2\delta^2)}$ the density of $N(0,\delta^2)$, the image measure has a density with respect to $R_m$:
--   $$(O_\delta)_*\Gamma_{\nu,m}=P_\delta\cdot R_m,\qquad P_\delta(A,y)=\int_E\prod_{j=1}^mg_{\delta^2}\bigl(y_j-\langle t,A_j\rangle\bigr)\,d\nu(t).$$
--
--   Thus the joint law of the design rows and the noisy labels is absolutely continuous with respect to (Gaussian rows) $\otimes$ (Lebesgue labels), and its density is the Gaussian mollification of the noiseless projection law. This identification makes moment bounds on $P_\delta$ applicable to the observation law.
--
--   **Formalization Note** The objects are `gaussianCoupling ν m`, `noisyObservation m δ`, `matrixLabelReference m` and `projectionSmoothing ν (gaussianPDF 0 v) m` with `v = δ^2`; the right-hand side is `Measure.withDensity`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Projection.lean#L53-L77

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian
import Definitions.Def_OAI_Probability_Subsphere_Regression_Projection

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]

theorem OAI.SubsphereRegression.gaussianCoupling_map_noisyObservation (ν : Measure E) [SigmaFinite ν]
    (m : ℕ) (δ : ℝ) (hδ : δ ≠ 0) :
    (gaussianCoupling ν m).map (noisyObservation m δ) =
      (matrixLabelReference (E := E) m).withDensity
        (projectionSmoothing ν (gaussianPDF 0 (NNReal.mk (δ^2) (sq_nonneg δ))) m) := by sorry
