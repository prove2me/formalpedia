-- Prove2me | Theorems.Thm_GlobalTheory_T_integral_heckeMellinGaussIntegrand_eq_prod_gamma
-- name    : GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T20:47:17.685814+00:00
-- url     : https://prove2.me/theorems/b1ed1ef5-f49a-4d73-855d-a21e7768799f
-- title:
--   T: integral hecke Mellin Gauss Integrand eq prod gamma
-- statement:
--   The T construction uses the integral hecke Mellin Gauss Integrand eq prod gamma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralHeckeMellinGaussIntegrandEqProdGammaStatement.lean#L10-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/IntegralHeckeMellinGaussIntegrandEqProdGammaStatement.lean#L10-L11

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGamma
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_CompletedLStripBounds
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormWt
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GaussZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_ContinuousTerm
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_GammaIntegralExpSubstitutionRealLineStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_IntegralHeckeMellinGaussIntegrandEqProdGammaStatement
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

theorem GlobalTheory.T.integral_heckeMellinGaussIntegrand_eq_prod_gamma : ∀ (I : Type) [Fintype I] (n : I → ℤ) (s : ℂ), 0 < s.re → ∀ v : I → ℂ, (∀ i, v i ≠ 0) → Integrable (GlobalTheory.HeckeMellin.term n s v) ∧ ∫ y, GlobalTheory.HeckeMellin.term n s v y = ∏ i, GlobalTheory.HeckeTheta.hmon (n i) (v i) * Complex.Gamma (s + ((|n i| : ℤ) : ℂ) / 2) * ((2 * Real.pi * ‖v i‖ ^ 2 : ℝ) : ℂ) ^ (-(s + ((|n i| : ℤ) : ℂ) / 2)) ∧ ∫ y, ‖GlobalTheory.HeckeMellin.term n s v y‖ = ∏ i, ‖v i‖ ^ (n i).natAbs * Real.Gamma (s.re + (|n i| : ℝ) / 2) * (2 * Real.pi * ‖v i‖ ^ 2) ^ (-(s.re + (|n i| : ℝ) / 2)) := by sorry
