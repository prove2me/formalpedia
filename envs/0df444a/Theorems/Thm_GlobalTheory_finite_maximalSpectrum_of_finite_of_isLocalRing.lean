-- Prove2me | Theorems.Thm_GlobalTheory_finite_maximalSpectrum_of_finite_of_isLocalRing
-- name    : GlobalTheory.finite_maximalSpectrum_of_finite_of_isLocalRing
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:26:48.060464+00:00
-- url     : https://prove2.me/theorems/94113e81-e1a3-4976-ac55-8ec18c07b9e3
-- title:
--   Global Theory: finite maximal Spectrum of finite of is Local Ring
-- statement:
--   The Global Theory construction uses the finite maximal Spectrum of finite of is Local Ring property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L111-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/FiniteMaximalSpectrumOfFiniteOfIsLocalRing.lean#L111-L117

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_FiniteMaximalSpectrumOfFiniteOfIsLocalRing
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory
open IsLocalRing Polynomial TensorProduct

theorem GlobalTheory.finite_maximalSpectrum_of_finite_of_isLocalRing (R S : Type*) [CommRing R] [IsLocalRing R]
    [CommRing S] [Algebra R S] [Module.Finite R S] : Finite (MaximalSpectrum S) := by sorry
