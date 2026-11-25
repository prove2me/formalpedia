-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_localIdeal_one_iff
-- name    : GroundTheory.Global.mem_localIdeal_one_iff
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:57:10.548616+00:00
-- url     : https://prove2.me/theorems/ae19cb26-4950-48c4-a422-0bfff550b08f
-- title:
--   Global: mem local Ideal one iff
-- statement:
--   The Global construction uses the mem local Ideal one iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L124-L128
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L124-L128

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

theorem GroundTheory.Global.mem_localIdeal_one_iff (v : HeightOneSpectrum (𝓞 K)) {y : v.adicCompletion K} :
    y ∈ localIdeal (1 : FractionalIdeal (𝓞 K)⁰ K) v ↔ y ∈ v.adicCompletionIntegers K := by sorry
