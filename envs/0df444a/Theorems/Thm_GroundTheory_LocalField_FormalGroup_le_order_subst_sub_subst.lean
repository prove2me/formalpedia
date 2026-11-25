-- Prove2me | Theorems.Thm_GroundTheory_LocalField_FormalGroup_le_order_subst_sub_subst
-- name    : GroundTheory.LocalField.FormalGroup.le_order_subst_sub_subst
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T12:59:00.806809+00:00
-- url     : https://prove2.me/theorems/7144eff7-7b01-413f-b43f-54640c49dbd3
-- title:
--   Formal Group: le order subst sub subst
-- statement:
--   The Formal Group construction uses the le order subst sub subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FormalGroups/Truncation.lean#L12-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FormalGroups/Truncation.lean#L12-L20

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
variable {σ τ R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

theorem GroundTheory.LocalField.FormalGroup.le_order_subst_sub_subst {a : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (ha0 : ∀ i, constantCoeff (a i) = 0) {f g : MvPowerSeries σ R} {n : ℕ∞}
    (h : n ≤ order (f - g)) : n ≤ order (subst a f - subst a g) := by sorry
