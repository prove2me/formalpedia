-- Prove2me | Theorems.Thm_GlobalTheory_gram_posSemidef_of_int_form
-- name    : GlobalTheory.gram_posSemidef_of_int_form
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:54:12.51794+00:00
-- url     : https://prove2.me/theorems/8b8316dc-22ab-4db7-9450-3181ca14f72c
-- title:
--   Global Theory: gram pos Semidef of int form
-- statement:
--   The Global Theory construction uses the gram pos Semidef of int form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramPosSemidefOfIntForm.lean#L7-L62
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramPosSemidefOfIntForm.lean#L7-L62

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramPosSemidefOfIntForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Matrix

theorem GlobalTheory.gram_posSemidef_of_int_form {X : Type} [AddCommGroup X] {r : ℕ}
    (b : LinearMap.BilinForm ℤ X) (hsymm : ∀ y z, b y z = b z y) (hpos : ∀ y, 0 ≤ b y y)
    (v : Fin r → X) : (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by sorry
