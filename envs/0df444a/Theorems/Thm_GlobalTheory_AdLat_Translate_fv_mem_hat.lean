-- Prove2me | Theorems.Thm_GlobalTheory_AdLat_Translate_fv_mem_hat
-- name    : GlobalTheory.AdLat.Translate.fv_mem_hat
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:02:48.491471+00:00
-- url     : https://prove2.me/theorems/c68d817a-0c60-453b-93c8-915f365fbd4b
-- title:
--   Translate: fv mem hat
-- statement:
--   The Translate construction uses the fv mem hat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeRationalVectorsInAdelicTranslate.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UnitaryExistence/ExistsLatticeRationalVectorsInAdelicTranslate.lean#L31-L32

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ExistenceOfLattices_Hat1
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_AdelicCompletionRationalPointsAndApproximation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UnitaryExistence_ExistsLatticeRationalVectorsInAdelicTranslate
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain GlobalTheory.AdLat
open scoped TensorProduct Matrix nonZeroDivisors
open GlobalTheory GlobalTheory.AdLat GlobalTheory.AdLat.Translate
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem GlobalTheory.AdLat.Translate.fv_mem_hat {S : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ S) : fv F x ∈ hat F S := by sorry
