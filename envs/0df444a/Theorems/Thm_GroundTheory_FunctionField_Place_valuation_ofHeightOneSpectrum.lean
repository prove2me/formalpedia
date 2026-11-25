-- Prove2me | Theorems.Thm_GroundTheory_FunctionField_Place_valuation_ofHeightOneSpectrum
-- name    : GroundTheory.FunctionField.Place.valuation_ofHeightOneSpectrum
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:54:07.683623+00:00
-- url     : https://prove2.me/theorems/0df548d9-571b-5119-8456-cd3101d40a84
-- title:
--   Place: valuation of Height One Spectrum
-- statement:
--   The Place construction uses the valuation of Height One Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBridge.lean#L121-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/FunctionField/PlaceBridge.lean#L121-L145

import Mathlib
import Definitions.Def_GroundTheory_FunctionField_PlaceSum
import Definitions.Def_GroundTheory_FunctionField_PlaceBridge
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.FunctionField
open IsDedekindDomain IsLocalRing
open scoped WithZero
open GroundTheory.FunctionField.Place
variable {k K : Type*} [Field k] [Field K] [Algebra k K]
variable (B : Type*) [CommRing B] [IsDedekindDomain B] [Algebra B K] [IsFractionRing B K]
  (hk : ∀ c : k, algebraMap k K c ∈ (algebraMap B K).range)
variable [IsFunctionField k K]

theorem GroundTheory.FunctionField.Place.valuation_ofHeightOneSpectrum (P : HeightOneSpectrum B) :
    (ofHeightOneSpectrum B hk P).valuation = P.valuation K := by sorry
