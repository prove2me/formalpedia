-- Prove2me | Theorems.Thm_GlobalTheory_HasQExpansion_unique
-- name    : GlobalTheory.HasQExpansion.unique
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T08:19:47.158032+00:00
-- url     : https://prove2.me/theorems/00d699df-5043-422a-b8c4-57798bd99401
-- title:
--   Has QExpansion: unique
-- statement:
--   The Has QExpansion construction uses the unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L128-L129
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L128-L129

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

theorem GlobalTheory.HasQExpansion.unique (hh : 0 < h) (hf : HasQExpansion h f φ) (hg : HasQExpansion h f ψ) : φ = ψ := by sorry
