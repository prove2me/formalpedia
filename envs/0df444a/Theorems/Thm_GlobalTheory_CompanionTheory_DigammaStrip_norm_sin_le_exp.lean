-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaStrip_norm_sin_le_exp
-- name    : GlobalTheory.CompanionTheory.DigammaStrip.norm_sin_le_exp
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:37:17.110746+00:00
-- url     : https://prove2.me/theorems/fb2dae7d-a0b5-42b1-93d5-c44579cda492
-- title:
--   Digamma Strip: norm sin le exp
-- statement:
--   The Digamma Strip construction uses the norm sin le exp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean#L19-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean#L19-L29

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

theorem GlobalTheory.CompanionTheory.DigammaStrip.norm_sin_le_exp (u : ℂ) : ‖Complex.sin u‖ ≤ Real.exp |u.im| := by sorry
