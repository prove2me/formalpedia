-- Prove2me | Theorems.Thm_OAI_GaussianPropeller_HeatConvolution_fderiv_heat
-- name    : OAI.GaussianPropeller.HeatConvolution.fderiv_heat
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T06:03:45.82051+00:00
-- url     : https://prove2.me/theorems/72808e3a-addf-4e20-bb93-6ff9482d8e16
-- title:
--   Differentiating the heat semigroup in space
-- statement:
--   Let $E=\mathbb R^\iota$ be a finite-dimensional Euclidean space with standard Gaussian measure $\gamma$, and for a function $F$ on $E$ let $P_tF(x)=\int F(x+\sqrt t\,z)\,d\gamma(z)$ be the Gaussian heat semigroup. Let $F:E\to V$ take values in a normed space, be bounded, and have a continuous bounded derivative $DF$. Then for all $t$ and $x$, $P_tF$ is differentiable at $x$ with
--   $$
--   D(P_tF)(x)=(P_tDF)(x)=\int DF\bigl(x+\sqrt t\,z\bigr)\,d\gamma(z).
--   $$
--
--   The heat semigroup commutes with differentiation.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianPropeller/HeatConvolution.lean#L48-L62

import Mathlib
import Definitions.Def_GaussianPropeller
import Definitions.Def_OAI_Probability_GaussianPropeller_Moments
import Definitions.Def_OAI_Probability_GaussianPropeller_Dual
import Definitions.Def_OAI_Probability_GaussianPropeller_Deletion
import Definitions.Def_OAI_Probability_GaussianPropeller_Translation
import Definitions.Def_OAI_Probability_GaussianPropeller_HeatConvolution

open OAI OAI.GaussianPropeller OAI.GaussianPropeller.HeatConvolution
universe uV uι
open MeasureTheory ProbabilityTheory
open scoped ENNReal
open scoped RealInnerProductSpace
open scoped RealInnerProductSpace
open MeasureTheory ProbabilityTheory Set
open scoped ENNReal RealInnerProductSpace
open Filter
open scoped Topology
variable {ι : Type uι} [Fintype ι]
local notation "E" => EuclideanSpace ℝ ι
local notation "γ" => stdGaussian E
variable {V : Type uV} [NormedAddCommGroup V]
variable [NormedSpace ℝ V] [CompleteSpace V]
    [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V]

theorem OAI.GaussianPropeller.HeatConvolution.fderiv_heat {F : E → V} {D : E → E →L[ℝ] V}
    (hD : ∀ x, HasFDerivAt F (D x) x) (hcD : Continuous D)
    {B C : ℝ} (hB : ∀ x, ‖F x‖ ≤ B) (hC : ∀ x, ‖D x‖ ≤ C)
    (t : ℝ) (x : E) : HasFDerivAt (heat F t) (heat D t x) x := by sorry
