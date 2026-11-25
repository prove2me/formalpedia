-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DigammaStrip_norm_digamma_le
-- name    : GlobalTheory.CompanionTheory.DigammaStrip.norm_digamma_le
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:00:42.476108+00:00
-- url     : https://prove2.me/theorems/bf3c4692-2913-4c11-8930-b61ce4c791bf
-- title:
--   Digamma Strip: norm digamma le
-- statement:
--   The Digamma Strip construction uses the norm digamma le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean#L109-L179
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/DigammaBoundVerticalStrip.lean#L109-L179

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

theorem GlobalTheory.CompanionTheory.DigammaStrip.norm_digamma_le :
    ∃ C : ℝ, 0 < C ∧ ∀ z : ℂ, 1 ≤ z.re → z.re ≤ 2 → 1 / 2 ≤ |z.im| →
      ‖digamma z‖ ≤ C * (1 + |z.im|) := by sorry
