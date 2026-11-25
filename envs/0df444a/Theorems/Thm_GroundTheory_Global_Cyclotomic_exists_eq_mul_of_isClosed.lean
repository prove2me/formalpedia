-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_exists_eq_mul_of_isClosed
-- name    : GroundTheory.Global.Cyclotomic.exists_eq_mul_of_isClosed
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T23:37:12.81996+00:00
-- url     : https://prove2.me/theorems/8e703e0c-adaa-4b4e-8e58-692b1d03fc14
-- title:
--   Cyclotomic: exists eq mul of is Closed
-- statement:
--   The Cyclotomic construction uses the exists eq mul of is Closed property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean#L126-L158
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean#L126-L158

import Mathlib
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ProfinitePadic
import Definitions.Def_GroundTheory_GlobalFields_CyclotomicCharacters_ClosedSubgroups
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
set_option synthInstance.maxHeartbeats 400000
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open scoped GroundTheory.LocalField.Abstract
open GroundTheory GroundTheory.Global
open GroundTheory.Global.Cyclotomic
open GroundTheory.LocalField.Abstract

theorem GroundTheory.Global.Cyclotomic.exists_eq_mul_of_isClosed (H : AddSubgroup ℤ̂) (hH : IsClosed (H : Set ℤ̂))
    (hne : ∀ q : Nat.Primes, ∃ h ∈ H, toPadicInt q h ≠ 0) :
    ∃ g : ℤ̂, (∀ q : Nat.Primes, toPadicInt q g ≠ 0) ∧ ∀ y, y ∈ H ↔ ∃ a, y = g * a := by sorry
