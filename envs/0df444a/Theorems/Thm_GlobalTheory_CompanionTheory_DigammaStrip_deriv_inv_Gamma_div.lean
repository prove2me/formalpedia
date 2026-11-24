-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaStrip_deriv_inv_Gamma_div
-- name    : GlobalTheory.CompanionTheory.DigammaStrip.deriv_inv_Gamma_div
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:36.209309+00:00
-- url     : https://prove2.me/theorems/11ef07dd-723f-4bf1-a27b-fb513754dd81
-- title:
--   Digamma Strip: deriv inv Gamma div
-- statement:
--   The Digamma Strip construction uses the deriv inv Gamma div property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean#L96-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean#L96-L107

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

theorem GlobalTheory.CompanionTheory.DigammaStrip.deriv_inv_Gamma_div {z : ℂ} (hz : 0 < z.re) :
    deriv (fun w => (Complex.Gamma w)⁻¹) z / (Complex.Gamma z)⁻¹ = -digamma z := by sorry
