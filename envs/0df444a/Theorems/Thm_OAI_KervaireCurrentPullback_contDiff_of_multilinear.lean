-- Prove2me | Theorems.Thm_OAI_KervaireCurrentPullback_contDiff_of_multilinear
-- name    : OAI.KervaireCurrentPullback.contDiff_of_multilinear
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:26:29.774411+00:00
-- url     : https://prove2.me/theorems/1f7958b9-3203-439c-a3ec-339ae483a927
-- title:
--   Smoothness of alternating-map-valued functions
-- statement:
--   Let $F,H$ be finite-dimensional and $f$ a map from a normed space $E$ to continuous alternating $n$-linear maps $F^n\to H$. If the composite with the inclusion is smooth,
--   $$
--   E\xrightarrow{f}\mathrm{Alt}^n(F;H)\hookrightarrow\mathrm{Mult}^n(F;H),
--   $$
--   then $f$ itself is smooth.
--
--   The alternating maps form a closed subspace of the multilinear maps, with the induced norm.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/CurrentPullback.lean#L30-L46

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

open OAI
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
variable {E F G H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

theorem OAI.KervaireCurrentPullback.contDiff_of_multilinear {n : ℕ} [FiniteDimensional ℝ F] [FiniteDimensional ℝ H]
    {f : E → F [⋀^Fin n]→L[ℝ] H}
    (hf : ContDiff ℝ ∞ (fun x ↦ (f x).toContinuousMultilinearMap)) :
    ContDiff ℝ ∞ f := by sorry
