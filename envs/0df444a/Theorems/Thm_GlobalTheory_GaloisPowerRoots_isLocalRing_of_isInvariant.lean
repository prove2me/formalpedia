-- Prove2me | Theorems.Thm_GlobalTheory_GaloisPowerRoots_isLocalRing_of_isInvariant
-- name    : GlobalTheory.GaloisPowerRoots.isLocalRing_of_isInvariant
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T13:48:51.899941+00:00
-- url     : https://prove2.me/theorems/e964f013-0393-4313-ac39-9bd71395aff2
-- title:
--   Galois Power Roots: is Local Ring of is Invariant
-- statement:
--   The Galois Power Roots construction uses the is Local Ring of is Invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSubMemMaximalIdeal.lean#L7-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsSubMemMaximalIdeal.lean#L7-L125

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsSubMemMaximalIdeal
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u_1
open Polynomial IsLocalRing
open scoped Pointwise
open GlobalTheory GlobalTheory.GaloisPowerRoots

theorem GlobalTheory.GaloisPowerRoots.isLocalRing_of_isInvariant {A B G : Type*} [CommRing A] [CommRing B] [IsDomain B]
    [Algebra A B] [FaithfulSMul A B] [Group G] [Finite G] [MulSemiringAction G B]
    [SMulCommClass G A B] [Algebra.IsInvariant A B G] [hH : HenselianLocalRing A] :
    IsLocalRing B := by sorry
