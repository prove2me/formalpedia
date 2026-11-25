-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_binary_quadratic_eq_unit_of_disc_isUnit
-- name    : GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:30:34.799138+00:00
-- url     : https://prove2.me/theorems/9ca00f7b-f5a7-4ca0-a4c9-ecbd8d383f22
-- title:
--   T: exists binary quadratic eq unit of disc is Unit
-- statement:
--   The T construction uses the exists binary quadratic eq unit of disc is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqAdicCompletionIntegersStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsEqAdicCompletionIntegersStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqAdicCompletionIntegers
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsEqAdicCompletionIntegersStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain NumberField
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_binary_quadratic_eq_unit_of_disc_isUnit : ∀ (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) (t n u : v.adicCompletionIntegers F), IsUnit (t ^ 2 - 4 * n) → IsUnit u → ∃ r s : v.adicCompletionIntegers F, r ^ 2 + t * r * s + n * s ^ 2 = u := by sorry
