-- Prove2me | Theorems.Thm_GroundTheory_Global_isDiscreteValuationRing_adicCompletionIntegers
-- name    : GroundTheory.Global.isDiscreteValuationRing_adicCompletionIntegers
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:56:30.023581+00:00
-- url     : https://prove2.me/theorems/7a4fa5f7-da70-5c2b-8a45-1feabce13e44
-- title:
--   Global: is Discrete Valuation Ring adic Completion Integers
-- statement:
--   The Global construction uses the is Discrete Valuation Ring adic Completion Integers property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/LocalFieldAtPlace.lean#L15-L17

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_LocalAtPlace
import Definitions.Def_GroundTheory_GlobalFields_LocalFieldAtPlace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField WithZero
open scoped WithZero
open GroundTheory GroundTheory.Global
variable {R : Type*} [CommRing R] [IsDedekindDomain R] {K : Type*} [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

theorem GroundTheory.Global.isDiscreteValuationRing_adicCompletionIntegers :
    IsDiscreteValuationRing (v.adicCompletionIntegers K) := by sorry
