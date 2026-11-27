-- Prove2me | Theorems.Thm_GlobalTheory_Tw_Model_nrm_twConj
-- name    : GlobalTheory.Tw.Model.nrm_twConj
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:41:47.939227+00:00
-- url     : https://prove2.me/theorems/3a985e21-80de-5ab4-9329-f675973e8bdf
-- title:
--   Model: nrm tw Conj
-- statement:
--   The Model construction uses the nrm tw Conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L84-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L84-L88

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_TwConj
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_MemCentIffTwConj
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
noncomputable section
open GlobalTheory GlobalTheory.Tw GlobalTheory.Tw.Model
variable {n : ℕ} {R : Type} [CommRing R] [StarRing R]

theorem GlobalTheory.Tw.Model.nrm_twConj {x δ : Matrix (Fin n) (Fin n) R} (hx : IsUnit x) :
    nrm (twConj x δ) = x⁻¹ * nrm δ * x := by sorry
