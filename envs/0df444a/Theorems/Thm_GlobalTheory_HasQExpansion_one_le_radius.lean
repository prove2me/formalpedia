-- Prove2me | Theorems.Thm_GlobalTheory_HasQExpansion_one_le_radius
-- name    : GlobalTheory.HasQExpansion.one_le_radius
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T14:02:06.739667+00:00
-- url     : https://prove2.me/theorems/db3cf3c8-6e64-4165-840e-3f7c201e20d6
-- title:
--   Has QExpansion: one le radius
-- statement:
--   The Has QExpansion construction uses the one le radius property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L19-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L19-L31

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

theorem GlobalTheory.HasQExpansion.one_le_radius (hh : 0 < h) (hf : HasQExpansion h f φ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ (fun m ↦ coeff m φ)).radius := by sorry
