-- Prove2me | Theorems.Thm_GlobalTheory_Tw_Model_Phi_transpose
-- name    : GlobalTheory.Tw.Model.Phi_transpose
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T16:01:43.684846+00:00
-- url     : https://prove2.me/theorems/58dfd924-43ec-4482-84a4-fb72988b5778
-- title:
--   Model: Phi transpose
-- statement:
--   The Model construction uses the Phi transpose property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L41-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Definitions/NonGaloisDescent/MemCentIffTwConj.lean#L41-L48

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
omit [StarRing R]

theorem GlobalTheory.Tw.Model.Phi_transpose : (Phi n R)ᵀ = ((-1 : R) ^ (n - 1)) • Phi n R := by sorry
