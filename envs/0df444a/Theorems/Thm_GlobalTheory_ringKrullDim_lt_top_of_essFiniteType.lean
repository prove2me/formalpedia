-- Prove2me | Theorems.Thm_GlobalTheory_ringKrullDim_lt_top_of_essFiniteType
-- name    : GlobalTheory.ringKrullDim_lt_top_of_essFiniteType
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T23:18:54.192634+00:00
-- url     : https://prove2.me/theorems/958b326b-4d6a-4d08-b9b8-4345d5b1a39e
-- title:
--   Global Theory: ring Krull Dim lt top of ess Finite Type
-- statement:
--   The Global Theory construction uses the ring Krull Dim lt top of ess Finite Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingKrullDimLtTopOfEssFiniteType.lean#L35-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/RingKrullDimLtTopOfEssFiniteType.lean#L35-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_RingKrullDimLtTopOfEssFiniteType
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open IsLocalRing
open GlobalTheory
open IsLocalRing

theorem GlobalTheory.ringKrullDim_lt_top_of_essFiniteType (D : Type) [CommRing D] [Algebra.EssFiniteType ℤ D] :
    ringKrullDim D < ⊤ := by sorry
