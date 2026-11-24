-- Prove2me | Theorems.Thm_GlobalTheory_Lyndon_monomial_eq_prod
-- name    : GlobalTheory.Lyndon.monomial_eq_prod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T18:19:55.486798+00:00
-- url     : https://prove2.me/theorems/093d498a-99b2-4b97-9ed1-d9584069431e
-- title:
--   Lyndon: monomial eq prod
-- statement:
--   The Lyndon construction uses the monomial eq prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L608-L617
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/PublishedTheorems/TwistedTraceFormula/RadfordShufflePolynomialHolds.lean#L608-L617

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

theorem GlobalTheory.Lyndon.monomial_eq_prod {σ : Type} (d : σ →₀ ℕ) :
    (MvPolynomial.monomial d (1 : K)) = ((Finsupp.toMultiset d).map MvPolynomial.X).prod := by sorry
