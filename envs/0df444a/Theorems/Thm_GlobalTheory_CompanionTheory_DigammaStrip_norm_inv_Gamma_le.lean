-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaStrip_norm_inv_Gamma_le
-- name    : GlobalTheory.CompanionTheory.DigammaStrip.norm_inv_Gamma_le
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T11:35:55.612019+00:00
-- url     : https://prove2.me/theorems/e190a2df-090c-46b3-9c9d-81569b8242e8
-- title:
--   Digamma Strip: norm inv Gamma le
-- statement:
--   The Digamma Strip construction uses the norm inv Gamma le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean#L31-L94
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean#L31-L94

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

theorem GlobalTheory.CompanionTheory.DigammaStrip.norm_inv_Gamma_le {K : ℝ} (hK0 : 0 < K)
    (hK : ∀ x : ℝ, 1 / 2 ≤ x → x ≤ 5 / 2 → Real.Gamma x ≤ K) {w : ℂ}
    (h1 : 1 / 2 ≤ w.re) (h2 : w.re ≤ 5 / 2) (h3 : 1 / 4 ≤ |w.im|) :
    ‖(Complex.Gamma w)⁻¹‖ ≤ 16 * K * Real.exp (Real.pi * |w.im|) := by sorry
