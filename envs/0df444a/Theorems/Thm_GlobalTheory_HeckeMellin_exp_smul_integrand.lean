-- Prove2me | Theorems.Thm_GlobalTheory_HeckeMellin_exp_smul_integrand
-- name    : GlobalTheory.HeckeMellin.exp_smul_integrand
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T14:06:29.695885+00:00
-- url     : https://prove2.me/theorems/e223d143-58c5-47f8-8565-1df55e2f6a17
-- title:
--   Hecke Mellin: exp smul integrand
-- statement:
--   The Hecke Mellin construction uses the exp smul integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GammaIntegralExpSubstitutionRealLine.lean#L25-L35
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GammaIntegralExpSubstitutionRealLine.lean#L25-L35

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLine
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
open GlobalTheory GlobalTheory.HeckeMellin
open Set

theorem GlobalTheory.HeckeMellin.exp_smul_integrand (w : ℂ) (c t : ℝ) :
    |Real.exp t| • (((Real.exp t : ℝ) : ℂ) ^ (w - 1) * Complex.exp (-((c : ℂ) * (Real.exp t : ℝ)))) =
      Complex.exp (w * t) * Complex.exp (-(c * Real.exp t : ℝ)) := by sorry
