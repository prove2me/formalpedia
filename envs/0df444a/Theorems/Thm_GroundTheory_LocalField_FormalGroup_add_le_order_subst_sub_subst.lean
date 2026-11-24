-- Prove2me | Theorems.Thm_GroundTheory_LocalField_FormalGroup_add_le_order_subst_sub_subst
-- name    : GroundTheory.LocalField.FormalGroup.add_le_order_subst_sub_subst
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:44:13.84507+00:00
-- url     : https://prove2.me/theorems/70032c80-c039-48ac-bf88-4b4e0625a1a4
-- title:
--   Formal Group: add le order subst sub subst
-- statement:
--   The Formal Group construction uses the add le order subst sub subst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FormalGroups/Truncation.lean#L77-L108
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/LocalFields/FormalGroups/Truncation.lean#L77-L108

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

theorem GroundTheory.LocalField.FormalGroup.add_le_order_subst_sub_subst {a b : σ → MvPowerSeries τ S} (ha : HasSubst a)
    (hb : HasSubst b) (ha0 : ∀ i, constantCoeff (a i) = 0)
    (hb0 : ∀ i, constantCoeff (b i) = 0) {n : ℕ∞} (hab : ∀ i, n ≤ order (a i - b i))
    {f : MvPowerSeries σ R} {m : ℕ∞} (hf : m ≤ order f) :
    n + m ≤ order (subst a f - subst b f) + 1 := by sorry
