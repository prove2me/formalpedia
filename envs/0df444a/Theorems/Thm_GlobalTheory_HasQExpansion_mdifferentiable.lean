-- Prove2me | Theorems.Thm_GlobalTheory_HasQExpansion_mdifferentiable
-- name    : GlobalTheory.HasQExpansion.mdifferentiable
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T08:20:11.455179+00:00
-- url     : https://prove2.me/theorems/9ddb35dd-dc7a-4e42-8a44-45663d11f773
-- title:
--   Has QExpansion: mdifferentiable
-- statement:
--   The Has QExpansion construction uses the mdifferentiable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L57-L66
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L57-L66

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

theorem GlobalTheory.HasQExpansion.mdifferentiable (hh : 0 < h) (hf : HasQExpansion h f φ) : MDiff f := by sorry
