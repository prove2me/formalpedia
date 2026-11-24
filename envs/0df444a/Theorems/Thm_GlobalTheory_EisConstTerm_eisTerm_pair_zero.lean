-- Prove2me | Theorems.Thm_GlobalTheory_EisConstTerm_eisTerm_pair_zero
-- name    : GlobalTheory.EisConstTerm.eisTerm_pair_zero
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:57:56.253803+00:00
-- url     : https://prove2.me/theorems/40ad95fc-462b-4602-b8ee-a83f6c600778
-- title:
--   Eis Const Term: eis Term pair zero
-- statement:
--   The Eis Const Term construction uses the eis Term pair zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L9-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HasSumHilbertEisensteinConstantTermPartialZeta.lean#L9-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_OmegaFactorization
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasSumHilbertEisensteinConstantTermPartialZeta
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped nonZeroDivisors
open NumberField GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization
open GlobalTheory GlobalTheory.EisConstTerm

theorem GlobalTheory.EisConstTerm.eisTerm_pair_zero (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (s : ℕ) (z : Emb F → ℂ) (a : F) :
    eisTerm (2 * s) 0 z (a, 0) = ((2 * (Real.pi : ℂ) * Complex.I) ^ (2 * s * Module.finrank ℚ F))⁻¹ *
      ((|((Algebra.norm ℚ a : ℚ) : ℝ)| : ℝ) : ℂ)⁻¹ ^ (2 * s) := by sorry
