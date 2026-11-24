-- Prove2me | Theorems.Thm_GlobalTheory_PsiTail_pow_le_exp
-- name    : GlobalTheory.PsiTail.pow_le_exp
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:51:12.357996+00:00
-- url     : https://prove2.me/theorems/ea9491f9-b040-4d51-aa31-70ef3dde28b9
-- title:
--   Psi Tail: pow le exp
-- statement:
--   The Psi Tail construction uses the pow le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/Gl2L2Integrality.lean#L10-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/Gl2L2Integrality.lean#L10-L16

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_PrimeCountAsymptoticInProgressions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_Gl2L2Integrality
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology MeasureTheory
open GlobalTheory GlobalTheory.PsiTail
open Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2a2

theorem GlobalTheory.PsiTail.pow_le_exp (b : ℝ) (hb : 0 < b) (n : ℕ) (x : ℝ) (hx : 0 ≤ x) :
    x ^ n ≤ (n.factorial / b ^ n) * Real.exp (b * x) := by sorry
