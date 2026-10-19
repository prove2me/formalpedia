-- Prove2me | Theorems.Thm_OAI_KervaireClosedCurrent_contDiff_multilinear_eval
-- name    : OAI.KervaireClosedCurrent.contDiff_multilinear_eval
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:22:38.068918+00:00
-- url     : https://prove2.me/theorems/713f9bd2-395c-477a-a4bf-5af1ac31a985
-- title:
--   Smoothness of a form evaluated on vector fields
-- statement:
--   Let $f$ be a smooth map from a normed space $E$ to continuous $n$-multilinear maps $E^n\to F$, and $V_1,\dots,V_n$ smooth vector fields on $E$. Then
--   $$
--   x\mapsto f(x)\bigl(V_1(x),\dots,V_n(x)\bigr)
--   $$
--   is smooth.
--
--   This is used to differentiate currents evaluated on right-invariant fields.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/GroupTheory/Kervaire/HaarCurrents.lean#L78-L105

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
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem OAI.KervaireClosedCurrent.contDiff_multilinear_eval {n : ℕ}
    {f : E → ContinuousMultilinearMap ℝ (fun _ : Fin n ↦ E) F}
    {V : Fin n → E → E} (hf : ContDiff ℝ ∞ f) (hV : ∀ i, ContDiff ℝ ∞ (V i)) :
    ContDiff ℝ ∞ (fun x ↦ f x (V · x)) := by sorry
