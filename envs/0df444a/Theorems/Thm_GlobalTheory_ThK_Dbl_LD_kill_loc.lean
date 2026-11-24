-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_kill_loc
-- name    : GlobalTheory.ThK.Dbl.LD.kill_loc
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:03:18.985802+00:00
-- url     : https://prove2.me/theorems/e31007c9-bcbf-41c4-bcdc-98b75f791963
-- title:
--   LD: kill loc
-- statement:
--   The LD construction uses the kill loc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean#L100-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean#L100-L127

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ExistsCompactOpenAddSubgroup
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_LocDistA
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology GlobalTheory.WeilM
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.LD

theorem GlobalTheory.ThK.Dbl.LD.kill_loc {V : Type} [AddCommGroup V] [TopologicalSpace V] [NonarchimedeanAddGroup V] [T2Space V]
    (l : (V → ℂ) →ₗ[ℂ] ℂ) {φ : V → ℂ} (hφ : φ ∈ SB V)
    (h : ∀ x, φ x ≠ 0 → ∃ U ∈ 𝓝 x, ∀ ψ ∈ SB V, (∀ y ∉ U, ψ y = 0) → l ψ = 0) : l φ = 0 := by sorry
