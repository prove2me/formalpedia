-- Prove2me | Theorems.Thm_GlobalTheory_HeckeMellinProd_coord
-- name    : GlobalTheory.HeckeMellinProd.coord
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T14:03:00.124572+00:00
-- url     : https://prove2.me/theorems/b633b156-437f-4862-b748-633aebafb7a6
-- title:
--   Hecke Mellin Prod: coord
-- statement:
--   The Hecke Mellin Prod construction uses the coord property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralHeckeMellinGaussIntegrandEqProdGamma.lean#L22-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralHeckeMellinGaussIntegrandEqProdGamma.lean#L22-L40

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

theorem GlobalTheory.HeckeMellinProd.coord (n : ℤ) (s : ℂ) (v : ℂ) (y : ℝ) :
    GlobalTheory.HeckeTheta.hmon n ((Real.exp (y / 2) : ℂ) * v) *
      Complex.exp ((-2 * Real.pi * ‖(Real.exp (y / 2) : ℂ) * v‖ ^ 2 : ℝ) : ℂ) * Complex.exp (s * (y : ℂ)) =
    GlobalTheory.HeckeTheta.hmon n v * fac (s + ((|n| : ℤ) : ℂ) / 2) (‖v‖ ^ 2) y := by sorry
