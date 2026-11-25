-- Prove2me | Theorems.Thm_GlobalTheory_T_gram_posSemidef_of_symm_nonneg_int_bilinForm
-- name    : GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:31:52.107823+00:00
-- url     : https://prove2.me/theorems/3c2aed20-a446-54c5-b4ba-67af66f48422
-- title:
--   T: gram pos Semidef of symm nonneg int bilin Form
-- statement:
--   The T construction uses the gram pos Semidef of symm nonneg int bilin Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramPosSemidefOfIntFormStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GramPosSemidefOfIntFormStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramPosSemidefOfIntForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GramPosSemidefOfIntFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.gram_posSemidef_of_symm_nonneg_int_bilinForm : ∀ {X : Type} [AddCommGroup X] {r : ℕ} (b : LinearMap.BilinForm ℤ X), (∀ y z, b y z = b z y) → (∀ y, 0 ≤ b y y) → ∀ v : Fin r → X, (Matrix.of fun i j => (b (v i) (v j) : ℝ)).PosSemidef := by sorry
