-- Prove2me | Theorems.Thm_GlobalTheory_JR_MeasTransport_map_selfDual
-- name    : GlobalTheory.JR.MeasTransport.map_selfDual
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T17:34:48.899338+00:00
-- url     : https://prove2.me/theorems/d8f52a23-030a-4e29-93fa-04524a86bd04
-- title:
--   Meas Transport: map self Dual
-- statement:
--   The Meas Transport construction uses the map self Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MapIsIsomSelfDualMeasureKerLEqPiHaar.lean#L135-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MapIsIsomSelfDualMeasureKerLEqPiHaar.lean#L135-L172

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MulMatMemUnitaryGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticStarStructure
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualMeasureExistsUniqueFourierInversion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MapIsIsomSelfDualMeasureKerLEqPiHaar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.MeasTransport
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.MeasTransport.map_selfDual [hU : Unram F E] [MeasurableSpace E] [BorelSpace E] (A : Et F E) (ψ : AddChar F ℂ) {r : ℕ}
    {x : A.K} {j : A.L ≃ₗ[E] (Fin r → E)} (hx : A.IsIsom x j) (μ : Measure A.L) (hμ : SelfDual μ (A.kerL ψ x)) :
    SelfDual (Measure.map j μ) (fun a b => ψ (trForm (F := F) r a b)) := by sorry
