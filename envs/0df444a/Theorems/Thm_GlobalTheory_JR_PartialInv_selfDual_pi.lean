-- Prove2me | Theorems.Thm_GlobalTheory_JR_PartialInv_selfDual_pi
-- name    : GlobalTheory.JR.PartialInv.selfDual_pi
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T17:34:32.29873+00:00
-- url     : https://prove2.me/theorems/36186f97-3611-488c-81e8-e4a2eb985687
-- title:
--   Partial Inv: self Dual pi
-- statement:
--   The Partial Inv construction uses the self Dual pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelPartialFourierColumnTwiceNegColumn.lean#L39-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/MixedModelPartialFourierColumnTwiceNegColumn.lean#L39-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_RowMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorPropertiesStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_SelfDualIffLatticeVolumeAndPlancherelStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_MixedModelPartialFourierColumnTwiceNegColumn
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
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.PartialInv

theorem GlobalTheory.JR.PartialInv.selfDual_pi (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [Unram F E] (r : ℕ) (M : Meas r F E) (ψ : AddChar F ℂ) (hψ : IsStdChar ψ) :
    letI := M.mF
    SelfDual (Measure.pi fun _ : Fin r => M.μF) (fun x y : Fin r → F => ψ (x ⬝ᵥ y)) := by sorry
