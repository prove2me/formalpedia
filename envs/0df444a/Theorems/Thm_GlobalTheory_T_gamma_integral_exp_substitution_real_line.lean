-- Prove2me | Theorems.Thm_GlobalTheory_T_gamma_integral_exp_substitution_real_line
-- name    : GlobalTheory.T.gamma_integral_exp_substitution_real_line
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T20:40:09.980824+00:00
-- url     : https://prove2.me/theorems/a3d8307e-7297-4361-a527-a89fe360f031
-- title:
--   T: gamma integral exp substitution real line
-- statement:
--   The T construction uses the gamma integral exp substitution real line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GammaIntegralExpSubstitutionRealLineStatement.lean#L9-L10
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/GammaIntegralExpSubstitutionRealLineStatement.lean#L9-L10

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLine
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLineStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField MeasureTheory
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.gamma_integral_exp_substitution_real_line : ∀ (r : ℝ), 0 < r → ∀ w : ℂ, 0 < w.re → Integrable (fun t : ℝ => Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ))) ∧ ∫ t : ℝ, Complex.exp (w * t) * Complex.exp (-(2 * Real.pi * r * Real.exp t : ℝ)) = Complex.Gamma w * ((2 * Real.pi * r : ℝ) : ℂ) ^ (-w) := by sorry
