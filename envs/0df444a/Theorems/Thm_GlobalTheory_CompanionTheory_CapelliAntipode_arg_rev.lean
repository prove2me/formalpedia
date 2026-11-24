-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_arg_rev
-- name    : GlobalTheory.CompanionTheory.CapelliAntipode.arg_rev
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:26:58.727489+00:00
-- url     : https://prove2.me/theorems/4f15c9e4-36e9-48e1-b9bd-13f99d1a7ee7
-- title:
--   Capelli Antipode: arg rev
-- statement:
--   The Capelli Antipode construction uses the arg rev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetOppositeNeg.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetOppositeNeg.lean#L33-L38

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_QuantumDetOppositeNeg
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.REAL
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CapelliAntipode

theorem GlobalTheory.CompanionTheory.CapelliAntipode.arg_rev {t : ℕ} (v : ℂ) (j : Fin t) :
    -(v - (((Fin.rev j : Fin t) : ℕ) : ℂ)) = ((t : ℂ) - 1 - v) - ((j : ℕ) : ℂ) := by sorry
