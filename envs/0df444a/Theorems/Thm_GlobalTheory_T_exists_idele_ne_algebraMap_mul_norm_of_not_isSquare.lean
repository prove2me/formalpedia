-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_idele_ne_algebraMap_mul_norm_of_not_isSquare
-- name    : GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T16:28:32.727801+00:00
-- url     : https://prove2.me/theorems/4410659c-21e1-465c-8aa5-45b4044c0622
-- title:
--   T: exists idele ne algebra Map mul norm of not is Square
-- statement:
--   The T construction uses the exists idele ne algebra Map mul norm of not is Square property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNormStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HeightProofs/ExistsIdeleNotMulNormStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNorm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_SqSubLeNormSub
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_SUnitsSupUnitsLocalNormsSqrtNeTop
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsAdmissibleLocalNormMemSUnitsSupGlobalNormStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HeightProofs_ExistsIdeleNotMulNormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IsDedekindDomain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_idele_ne_algebraMap_mul_norm_of_not_isSquare : ∀ (F : Type) [Field F] [NumberField F] (δ : F), ¬ IsSquare δ → ∃ a : (AdeleRing (𝓞 F) F)ˣ, ∀ (t : F) (x y : AdeleRing (𝓞 F) F), (a : AdeleRing (𝓞 F) F) ≠ algebraMap F (AdeleRing (𝓞 F) F) t * (x ^ 2 - algebraMap F (AdeleRing (𝓞 F) F) δ * y ^ 2) := by sorry
