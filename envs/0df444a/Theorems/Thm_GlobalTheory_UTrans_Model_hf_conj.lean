-- Prove2me | Theorems.Thm_GlobalTheory_UTrans_Model_hf_conj
-- name    : GlobalTheory.UTrans.Model.hf_conj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T13:10:57.857214+00:00
-- url     : https://prove2.me/theorems/a986704b-1337-4006-a5ba-220aaa16798e
-- title:
--   Model: hf conj
-- statement:
--   The Model construction uses the hf conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L31-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/AdelicHermitianForms/NontrivialTransvection.lean#L31-L35

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

theorem GlobalTheory.UTrans.Model.hf_conj (σ : R →+* R) (G : Matrix (Fin n) (Fin n) R) (hσ : ∀ a, σ (σ a) = a)
    (hG : ∀ a b, σ (G a b) = G b a) (x y : Fin n → R) : σ (hf σ G x y) = hf σ G y x := by sorry
