-- Prove2me | Theorems.Thm_GroundTheory_Global_mem_localIdeal_iff
-- name    : GroundTheory.Global.mem_localIdeal_iff
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T00:39:26.171492+00:00
-- url     : https://prove2.me/theorems/2698193f-b819-4961-9381-9eea0e9f12ff
-- title:
--   Global: mem local Ideal iff
-- statement:
--   The Global construction uses the mem local Ideal iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L85-L116
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L85-L116

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

theorem GroundTheory.Global.mem_localIdeal_iff {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) {y : v.adicCompletion K} :
    y ∈ localIdeal I v ↔ Valued.v y ≤ exp (-count K v I) := by sorry
