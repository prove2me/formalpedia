-- Prove2me | Theorems.Thm_GlobalTheory_HeckeMellinOne_ofReal_prod_cpow
-- name    : GlobalTheory.HeckeMellinOne.ofReal_prod_cpow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:03:10.213815+00:00
-- url     : https://prove2.me/theorems/a58a313a-3e20-4dc5-b3fa-a6a9db64f3a8
-- title:
--   Hecke Mellin One: of Real prod cpow
-- statement:
--   The Hecke Mellin One construction uses the of Real prod cpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeMellinGaussIntegralNonzeroInteger.lean#L34-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeMellinGaussIntegralNonzeroInteger.lean#L34-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGammaStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CmTypeProdNormSqEqAbsNormSpanStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HeckeMellinGaussIntegralNonzeroInteger
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellinOne

theorem GlobalTheory.HeckeMellinOne.ofReal_prod_cpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℂ) :
    (((∏ j ∈ t, f j : ℝ)) : ℂ) ^ w = ∏ j ∈ t, ((f j : ℝ) : ℂ) ^ w := by sorry
