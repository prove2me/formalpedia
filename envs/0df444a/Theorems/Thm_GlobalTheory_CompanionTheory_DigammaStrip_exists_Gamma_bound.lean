-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaStrip_exists_Gamma_bound
-- name    : GlobalTheory.CompanionTheory.DigammaStrip.exists_Gamma_bound
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T11:36:11.580172+00:00
-- url     : https://prove2.me/theorems/9cd36f75-9742-4762-bdf4-5b38d4356d06
-- title:
--   Digamma Strip: exists Gamma bound
-- statement:
--   The Digamma Strip construction uses the exists Gamma bound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean#L8-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean#L8-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ExplicitFormula_LGrowthGamma
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_DigammaBoundVerticalStrip
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DigammaStrip

theorem GlobalTheory.CompanionTheory.DigammaStrip.exists_Gamma_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 5 / 2 → Real.Gamma x ≤ K := by sorry
