-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CapelliAntipode_unop_qdet_op_neg
-- name    : GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T11:27:01.065297+00:00
-- url     : https://prove2.me/theorems/f743fa55-bd6c-4e24-828e-34194ffa4e41
-- title:
--   Capelli Antipode: unop qdet op neg
-- statement:
--   The Capelli Antipode construction uses the unop qdet op neg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetOppositeNeg.lean#L64-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/QuantumDetOppositeNeg.lean#L64-L79

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

theorem GlobalTheory.CompanionTheory.CapelliAntipode.unop_qdet_op_neg (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (X : Fin n → Fin n → A)
    (hX : GlRel X) (v : ℂ) :
    MulOpposite.unop (qdet (fun i j => MulOpposite.op (-X i j)) v) =
      ((-1 : ℂ) ^ n) • qdet X ((n : ℂ) - 1 - v) := by sorry
