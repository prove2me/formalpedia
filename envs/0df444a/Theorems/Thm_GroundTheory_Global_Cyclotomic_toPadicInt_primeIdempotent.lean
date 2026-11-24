-- Prove2me | Theorems.Thm_GroundTheory_Global_Cyclotomic_toPadicInt_primeIdempotent
-- name    : GroundTheory.Global.Cyclotomic.toPadicInt_primeIdempotent
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T23:37:48.032858+00:00
-- url     : https://prove2.me/theorems/2958c158-a5ce-4b78-bfb4-6513f61459b4
-- title:
--   Cyclotomic: to Padic Int prime Idempotent
-- statement:
--   The Cyclotomic construction uses the to Padic Int prime Idempotent property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean#L92-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/GroundTheory/GlobalFields/CyclotomicCharacters/ClosedSubgroups.lean#L92-L94

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

theorem GroundTheory.Global.Cyclotomic.toPadicInt_primeIdempotent (q q' : Nat.Primes) :
    toPadicInt q' (primeIdempotent q) = Pi.single (M := fun q : Nat.Primes => ℤ_[q]) q 1 q' := by sorry
