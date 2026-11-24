-- Prove2me | Theorems.Thm_GlobalTheory_RapidFourier_term_eq
-- name    : GlobalTheory.RapidFourier.term_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T19:13:30.699829+00:00
-- url     : https://prove2.me/theorems/c7c28597-c71c-4e1d-b0d0-368b89aa8398
-- title:
--   Rapid Fourier: term eq
-- statement:
--   The Rapid Fourier construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L61-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/ContDiffAndFderivTsumFourierOfRapid.lean#L61-L65

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ContDiffAndFderivTsumFourierOfRapid
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex Matrix
open scoped ContDiff BigOperators Real
open GlobalTheory
open GlobalTheory.RapidFourier

theorem GlobalTheory.RapidFourier.term_eq {n : ℕ} (a : ℂ) (ν : Fin n → ℤ) (x : Fin n → ℝ) :
    a * cexp (2 * π * I * ∑ k, (ν k : ℂ) * (x k : ℂ)) = wave a (linForm ν x) := by sorry
