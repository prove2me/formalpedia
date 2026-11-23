-- Prove2me | Theorems.Thm_GlobalTheory_HasQExpansion_of_hasSum_pow
-- name    : GlobalTheory.HasQExpansion.of_hasSum_pow
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T11:11:56.942081+00:00
-- url     : https://prove2.me/theorems/f7f17074-fd25-4289-a429-3200fa38d0df
-- title:
--   Has QExpansion: of has Sum pow
-- statement:
--   The Has QExpansion construction uses the of has Sum pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L131-L140
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/HasQExpansionModularForm.lean#L131-L140

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

theorem GlobalTheory.HasQExpansion.of_hasSum_pow {c : ℕ → ℂ} {e : ℕ} (he : e ≠ 0)
    (hf : ∀ τ : ℍ, HasSum (fun m ↦ c m * (𝕢 h τ ^ e) ^ m) (f τ)) :
    HasQExpansion h f (PowerSeries.mk fun k ↦ if e ∣ k then c (k / e) else 0) := by sorry
