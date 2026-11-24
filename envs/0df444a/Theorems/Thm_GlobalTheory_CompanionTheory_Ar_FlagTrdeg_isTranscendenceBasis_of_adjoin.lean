-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_FlagTrdeg_isTranscendenceBasis_of_adjoin
-- name    : GlobalTheory.CompanionTheory.Ar.FlagTrdeg.isTranscendenceBasis_of_adjoin
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:17:48.685121+00:00
-- url     : https://prove2.me/theorems/ea385a6d-ad53-436c-9781-2410fc71f087
-- title:
--   Flag Trdeg: is Transcendence Basis of adjoin
-- statement:
--   The Flag Trdeg construction uses the is Transcendence Basis of adjoin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/GenericFlagTrdegFormula.lean#L24-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GeometryProofs/GenericFlagTrdegFormula.lean#L24-L30

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_IsGenericFlag
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GeometryProofs_GenericFlagTrdegFormula
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.CompanionTheory.Ar
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.FlagTrdeg
open scoped IntermediateField.algebraAdjoinAdjoin

theorem GlobalTheory.CompanionTheory.Ar.FlagTrdeg.isTranscendenceBasis_of_adjoin {k K ι : Type} [Field k] [Field K] [Algebra k K] {x : ι → K}
    (hx : AlgebraicIndependent k x)
    (h : Algebra.IsAlgebraic (IntermediateField.adjoin k (Set.range x)) K) :
    IsTranscendenceBasis k x := by sorry
