-- Prove2me | Theorems.Thm_GlobalTheory_JR_MeasTransport_trForm_sepLeft
-- name    : GlobalTheory.JR.MeasTransport.trForm_sepLeft
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:34:59.30991+00:00
-- url     : https://prove2.me/theorems/5ae28e60-9f0f-45b5-a55d-24914de2e5f3
-- title:
--   Meas Transport: tr Form sep Left
-- statement:
--   The Meas Transport construction uses the tr Form sep Left property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MapIsIsomSelfDualMeasureKerLEqPiHaar.lean#L38-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MapIsIsomSelfDualMeasureKerLEqPiHaar.lean#L38-L48

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

theorem GlobalTheory.JR.MeasTransport.trForm_sepLeft [hU : Unram F E] (r : ℕ) (c : Fin r → E) (h : ∀ b, trForm (F := F) r c b = 0) : c = 0 := by sorry
