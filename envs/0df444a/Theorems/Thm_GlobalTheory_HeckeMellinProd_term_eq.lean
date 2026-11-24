-- Prove2me | Theorems.Thm_GlobalTheory_HeckeMellinProd_term_eq
-- name    : GlobalTheory.HeckeMellinProd.term_eq
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T14:03:36.89298+00:00
-- url     : https://prove2.me/theorems/e8ae2659-2c99-4ac8-8f6c-65a68e180b72
-- title:
--   Hecke Mellin Prod: term eq
-- statement:
--   The Hecke Mellin Prod construction uses the term eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralHeckeMellinGaussIntegrandEqProdGamma.lean#L42-L48
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralHeckeMellinGaussIntegrandEqProdGamma.lean#L42-L48

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGamma
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
noncomputable section
open GlobalTheory GlobalTheory.HeckeMellinProd

theorem GlobalTheory.HeckeMellinProd.term_eq (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ) (v : I → ℂ) (y : I → ℝ) :
    GlobalTheory.HeckeMellin.term n s v y =
      ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * fac (s + ((|n i| : ℤ) : ℂ) / 2) (‖v i‖ ^ 2) (y i) := by sorry
