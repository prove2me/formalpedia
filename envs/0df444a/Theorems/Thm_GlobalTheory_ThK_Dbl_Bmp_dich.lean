-- Prove2me | Theorems.Thm_GlobalTheory_ThK_Dbl_Bmp_dich
-- name    : GlobalTheory.ThK.Dbl.Bmp.dich
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:41:08.0228+00:00
-- url     : https://prove2.me/theorems/b915bfc1-1d87-44d8-a8b6-da3d40b1e483
-- title:
--   Bmp: dich
-- statement:
--   The Bmp construction uses the dich property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/MemLam.lean#L125-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/WeilBound/ThetaLifts/LatticeBasics/MemLam.lean#L125-L210

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
variable {a : O} {n d : ℕ}

theorem GlobalTheory.ThK.Dbl.Bmp.dich [IsLocalRing O] (ψ : AddChar K ℂ) (hψ : ∀ x, (∀ y : O, ψ (x * algebraMap O K y) = 1) ↔ x ∈ (algebraMap O K).range)
    (h0 : a ≠ 0) (ha : a ∈ IsLocalRing.maximalIdeal O) (y : Matrix (Fin n) (Fin d) O) (r : Matrix (Fin d) (Fin n) O) (hr : y * r = 1)
    (h : GL (Fin n) K) : (h.1 - 1 ∈ lam K a n n ∧ (h⁻¹).1 - 1 ∈ lam K a n n) ∨ ∃ l : Matrix (Fin n) (Fin d) K →ₗ[K] K,
      (∀ Y ∈ lam K a n d, ψ (l Y) = 1 ∧ ψ (l (h.1 * Y)) = 1) ∧ ψ (l (h.1 * y.map (algebraMap O K) - y.map (algebraMap O K))) ≠ 1 := by sorry
