-- Prove2me | Theorems.Thm_GroundTheory_Global_le_exp_sub_one_of_lt
-- name    : GroundTheory.Global.le_exp_sub_one_of_lt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T01:13:33.436219+00:00
-- url     : https://prove2.me/theorems/10acf8c7-0047-4b4a-9962-103215a45ea1
-- title:
--   Global: le exp sub one of lt
-- statement:
--   The Global construction uses the le exp sub one of lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L46-L51
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L46-L51

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_IdeleGroups_ClassGroup
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_IdeleAction
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
set_option maxSynthPendingDepth 1
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum WithZero FractionalIdeal
open scoped NumberField.AdeleRing nonZeroDivisors
noncomputable section
variable {K : Type*} [Field K] [NumberField K]

theorem GroundTheory.Global.le_exp_sub_one_of_lt {y : ℤᵐ⁰} {n : ℤ} (h : y < exp n) : y ≤ exp (n - 1) := by sorry
