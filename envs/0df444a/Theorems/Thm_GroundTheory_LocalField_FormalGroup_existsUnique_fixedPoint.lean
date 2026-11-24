-- Prove2me | Theorems.Thm_GroundTheory_LocalField_FormalGroup_existsUnique_fixedPoint
-- name    : GroundTheory.LocalField.FormalGroup.existsUnique_fixedPoint
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:05.910809+00:00
-- url     : https://prove2.me/theorems/2d63b5a4-7907-4c9f-99be-8ec53941c3d3
-- title:
--   Formal Group: exists Unique fixed Point
-- statement:
--   The Formal Group construction uses the exists Unique fixed Point property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FormalGroups/Truncation.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FormalGroups/Truncation.lean#L116-L120

import Mathlib
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_ExistsUniqueFixedPoint
import Definitions.Def_GroundTheory_LocalFields_FormalGroups_Truncation
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open GroundTheory GroundTheory.LocalField GroundTheory.LocalField.FormalGroup
open MvPowerSeries
variable {σ R : Type*} [CommRing R]

theorem GroundTheory.LocalField.FormalGroup.existsUnique_fixedPoint (Φ : MvPowerSeries σ R → MvPowerSeries σ R)
    (hΦ : ∀ f g : MvPowerSeries σ R, ∀ n : ℕ, (n : ℕ∞) ≤ order (f - g) →
      ((n + 1 : ℕ) : ℕ∞) ≤ order (Φ f - Φ g)) :
    ∃! f, Φ f = f := by sorry
