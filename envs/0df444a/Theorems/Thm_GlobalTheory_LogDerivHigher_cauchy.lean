-- Prove2me | Theorems.Thm_GlobalTheory_LogDerivHigher_cauchy
-- name    : GlobalTheory.LogDerivHigher.cauchy
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:16:59.292664+00:00
-- url     : https://prove2.me/theorems/91a2c4bf-b07b-437c-9512-e5e0461aa1f6
-- title:
--   Log Deriv Higher: cauchy
-- statement:
--   The Log Deriv Higher construction uses the cauchy property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L47-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L47-L60

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_LogDerivLFunctionStrip
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_NormSubOneMulRiemannZetaLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical
open GlobalTheory GlobalTheory.LogDerivHigher

theorem GlobalTheory.LogDerivHigher.cauchy (K : ℝ) (U : Set ℂ) (hU : IsOpen U) (Z : Finset ℂ) (g : ℂ → ℂ)
    (h1 : DifferentiableOn ℂ g (U \ Z)) (h2 : ∀ z ∈ U \ (Z : Set ℂ), ‖g z‖ ≤ K)
    (s : ℂ) (R : ℝ) (hR : 0 < R) (hs : s ∉ Z) (hsub : Metric.closedBall s R ⊆ U) (k : ℕ) :
    ‖iteratedDeriv k g s‖ ≤ k.factorial * K / R ^ k := by sorry
