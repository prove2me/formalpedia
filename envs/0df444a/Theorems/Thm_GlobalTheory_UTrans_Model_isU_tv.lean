-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Model_isU_tv
-- name    : GlobalTheory.UTrans.Model.isU_tv
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:20:51.347504+00:00
-- url     : https://prove2.me/theorems/06b68bce-5766-4303-a2f2-7efd4a7e05d1
-- title:
--   Model: is U tv
-- statement:
--   The Model construction uses the is U tv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L37-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L37-L43

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_IsHermHyperbolic
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_NontrivialTransvection
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UTrans GlobalTheory.UTrans.Model
open GlobalTheory.UTrans
variable {R : Type} [CommRing R] {n : ℕ}

theorem GlobalTheory.UTrans.Model.isU_tv (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a)
    (hG : ∀ a b, σ (G a b) = G b a) (x : Fin n → R) (t : R)
    (h : t + σ t + t * σ t * hf σ G x x = 0) : IsU σ G (tv σ G x t) := by sorry
