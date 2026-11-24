-- Prove2me | Theorems.Thm_GlobalTheory_TripleIntertwiner_gauss_pow_four
-- name    : GlobalTheory.TripleIntertwiner.gauss_pow_four
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T21:12:17.715036+00:00
-- url     : https://prove2.me/theorems/da08d29d-fe52-402c-96a7-90b8ac8bbf56
-- title:
--   Triple Intertwiner: gauss pow four
-- statement:
--   The Triple Intertwiner construction uses the gauss pow four property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L70-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/GaussPowFourHom.lean#L70-L82

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_GaussPowFourHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.TripleIntertwiner
open Classical

theorem GlobalTheory.TripleIntertwiner.gauss_pow_four {M : Type*} [AddCommGroup M] [Fintype M] (β : M → M → ℂ)
    (hl : ∀ x x' y, β (x + x') y = β x y * β x' y) (hr : ∀ x y y', β x (y + y') = β x y * β x y')
    (hne : ∀ x y, β x y ≠ 0) :
    (∑ m, β m m) ^ 4 = (∑ m, (β m m)⁻¹) ^ 4 := by sorry
