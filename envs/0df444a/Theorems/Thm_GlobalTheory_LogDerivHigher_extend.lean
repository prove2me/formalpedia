-- Prove2me | Theorems.Thm_GlobalTheory_LogDerivHigher_extend
-- name    : GlobalTheory.LogDerivHigher.extend
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T18:18:53.135143+00:00
-- url     : https://prove2.me/theorems/33a3f05b-3e2a-4034-8feb-875ea091f439
-- title:
--   Log Deriv Higher: extend
-- statement:
--   The Log Deriv Higher construction uses the extend property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L10-L45
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L10-L45

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

theorem GlobalTheory.LogDerivHigher.extend (K : ℝ) (U : Set ℂ) (hU : IsOpen U) (Z : Finset ℂ) :
    ∀ g : ℂ → ℂ, DifferentiableOn ℂ g (U \ Z) → (∀ z ∈ U \ (Z : Set ℂ), ‖g z‖ ≤ K) →
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G U ∧ (∀ z, z ∉ Z → G z = g z) ∧ ∀ z ∈ U, ‖G z‖ ≤ K := by sorry
