-- Prove2me | Theorems.Thm_GlobalTheory_HasQExpansion_mul
-- name    : GlobalTheory.HasQExpansion.mul
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:42.490868+00:00
-- url     : https://prove2.me/theorems/5dfcd8d0-d6f0-4159-989b-d5cfe1b9414a
-- title:
--   Has QExpansion: mul
-- statement:
--   The Has QExpansion construction uses the mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L79-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L79-L90

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

theorem GlobalTheory.HasQExpansion.mul (hf : HasQExpansion h f φ) (hg : HasQExpansion h g ψ) :
    HasQExpansion h (fun τ ↦ f τ * g τ) (φ * ψ) := by sorry
