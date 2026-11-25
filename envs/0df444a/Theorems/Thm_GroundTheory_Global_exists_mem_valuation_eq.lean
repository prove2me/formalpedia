-- Prove2me | Theorems.Thm_GroundTheory_Global_exists_mem_valuation_eq
-- name    : GroundTheory.Global.exists_mem_valuation_eq
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T01:13:45.653654+00:00
-- url     : https://prove2.me/theorems/086e6d9a-6bc6-476a-9a4d-4046dcf5e044
-- title:
--   Global: exists mem valuation eq
-- statement:
--   The Global construction uses the exists mem valuation eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L53-L75
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/IdeleAction.lean#L53-L75

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

theorem GroundTheory.Global.exists_mem_valuation_eq {I : FractionalIdeal (𝓞 K)⁰ K} (hI : I ≠ 0)
    (v : HeightOneSpectrum (𝓞 K)) : ∃ a ∈ I, v.valuation K a = exp (-count K v I) := by sorry
