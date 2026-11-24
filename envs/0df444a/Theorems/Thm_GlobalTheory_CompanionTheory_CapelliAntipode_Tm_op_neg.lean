-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_Tm_op_neg
-- name    : GlobalTheory.CompanionTheory.CapelliAntipode.Tm_op_neg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:26:59.225728+00:00
-- url     : https://prove2.me/theorems/625a2207-ff90-4a22-9608-63536ac5293c
-- title:
--   Capelli Antipode: Tm op neg
-- statement:
--   The Capelli Antipode construction uses the Tm op neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetOppositeNeg.lean#L25-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetOppositeNeg.lean#L25-L31

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

theorem GlobalTheory.CompanionTheory.CapelliAntipode.Tm_op_neg {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (X : Fin n → Fin n → A) (w : ℂ)
    (i j : Fin n) :
    Tm (fun i j => MulOpposite.op (-X i j)) w i j = MulOpposite.op (-(Tm X (-w) i j)) := by sorry
