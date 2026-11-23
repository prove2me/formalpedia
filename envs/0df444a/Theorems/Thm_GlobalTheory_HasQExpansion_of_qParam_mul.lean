-- Prove2me | Theorems.Thm_GlobalTheory_HasQExpansion_of_qParam_mul
-- name    : GlobalTheory.HasQExpansion.of_qParam_mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:43.550827+00:00
-- url     : https://prove2.me/theorems/e62bb77a-c2a0-442d-bd3f-366139f9e480
-- title:
--   Has QExpansion: of q Param mul
-- statement:
--   The Has QExpansion construction uses the of q Param mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L107-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L107-L116

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_HasQExpansionModularForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open UpperHalfPlane ModularForm Complex Function Filter PowerSeries
open scoped Topology MatrixGroups Manifold Real
noncomputable section
open GlobalTheory
local notation "𝕢" => Function.Periodic.qParam
open GlobalTheory.HasQExpansion
variable {h : ℝ} {f g : ℍ → ℂ} {φ ψ : PowerSeries ℂ}

theorem GlobalTheory.HasQExpansion.of_qParam_mul (hf : HasQExpansion h (fun τ ↦ 𝕢 h τ * f τ) (X * φ)) :
    HasQExpansion h f φ := by sorry
