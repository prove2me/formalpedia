-- Prove2me | Theorems.Thm_GroundTheory_Global_eventually_isUnit_localizationAt
-- name    : GroundTheory.Global.eventually_isUnit_localizationAt
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T23:40:31.076518+00:00
-- url     : https://prove2.me/theorems/33119e5c-0295-4a96-b561-7767c477e155
-- title:
--   Global: eventually is Unit localization At
-- statement:
--   The Global construction uses the eventually is Unit localization At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean#L49-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/ComplexMultiplication/PrimeLocalization.lean#L49-L53

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_ComplexMultiplication_PrimeLocalization
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.Global
open NumberField IsDedekindDomain Polynomial
noncomputable section
variable (L : Type*) [Field L] [NumberField L]
variable {L}

theorem GroundTheory.Global.eventually_isUnit_localizationAt {x : L} (hx : x ≠ 0) :
    ∀ᶠ v : HeightOneSpectrum (𝓞 L) in Filter.cofinite,
      ∃ h : x ∈ localizationAt L v, IsUnit (⟨x, h⟩ : localizationAt L v) := by sorry
