-- Prove2me | Theorems.Thm_GlobalTheory_HeckeMellinOne_real_prod_rpow
-- name    : GlobalTheory.HeckeMellinOne.real_prod_rpow
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T14:03:05.185558+00:00
-- url     : https://prove2.me/theorems/fea9c1f8-418a-4293-89ab-898c34e7a0d5
-- title:
--   Hecke Mellin One: real prod rpow
-- statement:
--   The Hecke Mellin One construction uses the real prod rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeMellinGaussIntegralNonzeroInteger.lean#L83-L90
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/HeckeMellinGaussIntegralNonzeroInteger.lean#L83-L90

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

theorem GlobalTheory.HeckeMellinOne.real_prod_rpow {J : Type} (t : Finset J) (f : J → ℝ) (hf : ∀ j, 0 ≤ f j) (w : ℝ) :
    (∏ j ∈ t, f j) ^ w = ∏ j ∈ t, f j ^ w := by sorry
