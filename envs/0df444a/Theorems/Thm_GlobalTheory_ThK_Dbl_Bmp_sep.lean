-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Bmp_sep
-- name    : GlobalTheory.ThK.Dbl.Bmp.sep
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:03:29.015852+00:00
-- url     : https://prove2.me/theorems/640a0e84-071b-4f1f-ab58-eaaad085e492
-- title:
--   Bmp: sep
-- statement:
--   The Bmp construction uses the sep property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/MemLam.lean#L11-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/MemLam.lean#L11-L54

import Mathlib
import Definitions.Def_Development_WeilBound_ThetaLifts_LatticeBasics_MemLam
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ThK GlobalTheory.ThK.Dbl GlobalTheory.ThK.Dbl.Bmp
open Matrix
variable {O K : Type} [CommRing O] [IsDomain O] [IsPrincipalIdealRing O] [Field K] [Algebra O K] [IsFractionRing O K]

theorem GlobalTheory.ThK.Dbl.Bmp.sep (ψ : AddChar K ℂ) (hψ : ∀ x, (∀ y : O, ψ (x * algebraMap O K y) = 1) ↔ x ∈ (algebraMap O K).range)
    {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (L : Submodule O V) [L.IsLattice K] {y : V}
    (hy : y ∉ L) : ∃ l : V →ₗ[K] K, (∀ z ∈ L, ψ (l z) = 1) ∧ ψ (l y) ≠ 1 := by sorry
