-- Prove2me | Theorems.Thm_GlobalTheory_CxPointsSep_exists_det_ne_zero
-- name    : GlobalTheory.CxPointsSep.exists_det_ne_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T12:03:15.036504+00:00
-- url     : https://prove2.me/theorems/6a3de0a9-80fc-5650-942d-784928a2022e
-- title:
--   Cx Points Sep: exists det ne zero
-- statement:
--   The Cx Points Sep construction uses the exists det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfForallAlgHom.lean#L43-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/EqZeroOfForallAlgHom.lean#L43-L107

import Mathlib
import Definitions.Def_ReciprocityTheory_AnalyticForms_RegularLocalRings_BaseChangeCA
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_EqZeroOfForallAlgHom
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open TensorProduct
noncomputable section
open GlobalTheory GlobalTheory.CxPointsSep

theorem GlobalTheory.CxPointsSep.exists_det_ne_zero (B : Type) [CommRing B] [IsDomain B] [CharZero B] [Algebra.FiniteType ℤ B]
    (r : ℕ) (f : Fin r → B) (hf : LinearIndependent ℤ f) :
    ∃ x : Fin r → (B →+* ℂ), (Matrix.of fun i j => x i (f j)).det ≠ 0 := by sorry
