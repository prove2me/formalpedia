-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_aeval_injective
-- name    : GlobalTheory.Lyndon.aeval_injective
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:19:31.255552+00:00
-- url     : https://prove2.me/theorems/9f35fb19-5f45-476a-b19a-5031339e4480
-- title:
--   Lyndon: aeval injective
-- statement:
--   The Lyndon construction uses the aeval injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L619-L659
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L619-L659

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_PublishedTheorems_TwistedTraceFormula_RadfordShufflePolynomialHolds
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory
open Shuffle
open GlobalTheory.Lyndon
variable {A : Type} [LinearOrder A]
open ShuffleAlgebra
variable (K : Type) [Field K]

theorem GlobalTheory.Lyndon.aeval_injective [CharZero K] : Function.Injective
    (MvPolynomial.aeval (fun l : {w : List A // IsLyndon w} => word K l.1) :
      MvPolynomial {w : List A // IsLyndon w} K →ₐ[K] ShuffleAlgebra K A) := by sorry
