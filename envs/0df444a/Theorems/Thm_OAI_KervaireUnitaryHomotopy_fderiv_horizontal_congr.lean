-- Prove2me | Theorems.Thm_OAI_KervaireUnitaryHomotopy_fderiv_horizontal_congr
-- name    : OAI.KervaireUnitaryHomotopy.fderiv_horizontal_congr
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:35:43.648983+00:00
-- url     : https://prove2.me/theorems/14e557a2-f5f6-4f56-9f0c-eea8f2ae436e
-- title:
--   Maps agreeing on unitaries have equal tangential derivatives
-- statement:
--   Let $E$ be a finite-dimensional C*-algebra and $f,g:\mathbb R\times E\to D$ smooth. If $f(t,x)=g(s,x)$ for every unitary $x$, then for every unitary $x$ and skew-adjoint $a$,
--   $$
--   df_{(t,x)}(0,xa)=dg_{(s,x)}(0,xa).
--   $$
--
--   Derivatives along directions tangent to the unitary group only see the values on unitaries.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/UnitaryHomotopy.lean#L69-L97

import Mathlib
import Definitions.Def_Kervaire
import Definitions.Def_OAI_GroupTheory_Kervaire_Reductions
import Definitions.Def_OAI_GroupTheory_Kervaire_PermutationCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_Components
import Definitions.Def_OAI_GroupTheory_Kervaire_Suppression
import Definitions.Def_OAI_GroupTheory_Kervaire_ComponentFibers
import Definitions.Def_OAI_GroupTheory_Kervaire_StrongLimits
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralMeasures
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralLogarithm
import Definitions.Def_OAI_GroupTheory_Kervaire_ScalarPhase
import Definitions.Def_OAI_GroupTheory_Kervaire_TraceCalculus
import Definitions.Def_OAI_GroupTheory_Kervaire_SpectralApproximation
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseSubadditivity
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseNaturality
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseGrids
import Definitions.Def_OAI_GroupTheory_Kervaire_RegularOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixTrace
import Definitions.Def_OAI_GroupTheory_Kervaire_MatrixShifts
import Definitions.Def_OAI_GroupTheory_Kervaire_WeightedCycles
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseFaithfulness
import Definitions.Def_OAI_GroupTheory_Kervaire_PhaseDimension
import Definitions.Def_OAI_GroupTheory_Kervaire_MixingOperators
import Definitions.Def_OAI_GroupTheory_Kervaire_HaarCurrents
import Definitions.Def_OAI_GroupTheory_Kervaire_CurrentPullback
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceSpaces
import Definitions.Def_OAI_GroupTheory_Kervaire_IncidenceTangent
import Definitions.Def_OAI_GroupTheory_Kervaire_UnitaryHomotopy

open OAI OAI.KervaireUnitaryHomotopy
open Filter
open scoped Topology
open scoped CompactlySupported ComplexOrder
open MeasureTheory Filter
open scoped Topology
open Filter
open scoped Topology
open scoped ComplexOrder
open scoped lp ComplexConjugate
open scoped ComplexOrder
open MeasureTheory Measure Set Filter
open scoped Topology
open MeasureTheory ContinuousAlternatingMap Set VectorField
open scoped Topology ContDiff
open ContinuousAlternatingMap
open scoped ContDiff
open MeasureTheory NormedSpace
open scoped ContDiff
open Module Set ContinuousAlternatingMap
open Matrix Module
open scoped ContDiff Matrix.Norms.L2Operator
open scoped ComplexOrder
open scoped ContDiff
attribute [local instance] OAI.KervaireUnitaryHomotopy.instNormedAlgebraRat_oAI
variable (B C : Type*) [CStarAlgebra B] [CStarAlgebra C]
variable {B C}
variable {E D : Type*} [NormedRing E] [NormedAlgebra ℝ E] [CompleteSpace E]
  [StarRing E] [ContinuousStar E] [StarModule ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem OAI.KervaireUnitaryHomotopy.fderiv_horizontal_congr {f g : ℝ × E → D}
    (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g) (t s : ℝ)
    (heq : ∀ x : unitary E, f (t,(x : E)) = g (s,(x : E)))
    (x : unitary E) (a : skewAdjoint.submodule ℝ E) :
    fderiv ℝ f (t,(x : E)) (0,(x : E)*(a : E)) =
      fderiv ℝ g (s,(x : E)) (0,(x : E)*(a : E)) := by sorry
