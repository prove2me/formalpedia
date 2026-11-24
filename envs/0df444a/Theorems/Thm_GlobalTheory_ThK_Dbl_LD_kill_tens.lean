-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_LD_kill_tens
-- name    : GlobalTheory.ThK.Dbl.LD.kill_tens
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-24T21:03:13.830329+00:00
-- url     : https://prove2.me/theorems/d27a0478-667e-4c92-b682-da583d389eac
-- title:
--   LD: kill tens
-- statement:
--   The LD construction uses the kill tens property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean#L59-L98
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/LocDistA.lean#L59-L98

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

theorem GlobalTheory.ThK.Dbl.LD.kill_tens {X V : Type} [TopologicalSpace X] [T2Space X] [AddCommGroup V] [TopologicalSpace V]
    [NonarchimedeanAddGroup V] [LocallyCompactSpace V] [T2Space V] (S : Set X) (l : (X × V → ℂ) →ₗ[ℂ] ℂ)
    (h : ∀ f ∈ SB X, (∀ x ∉ S, f x = 0) → ∀ g ∈ SB V, l (fun z => f z.1 * g z.2) = 0)
    {F : X × V → ℂ} (hF : F ∈ SB (X × V)) (hS : ∀ z : X × V, z.1 ∉ S → F z = 0) : l F = 0 := by sorry
