-- Prove2me | Theorems.Thm_GlobalTheory_LogDerivHigher_iter
-- name    : GlobalTheory.LogDerivHigher.iter
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T18:18:56.985823+00:00
-- url     : https://prove2.me/theorems/bb9bb4af-c914-48e0-97f8-5a659d8a7e46
-- title:
--   Log Deriv Higher: iter
-- statement:
--   The Log Deriv Higher construction uses the iter property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L73-L101
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/IteratedDerivLogDerivDirichletLViaNearbyZeros.lean#L73-L101

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

theorem GlobalTheory.LogDerivHigher.iter (f : ℕ → ℂ) (hf : LSeries.abscissaOfAbsConv f ≤ 1) (e : ℂ) (Z : Finset ℂ) (m : ℂ → ℂ)
    (hZ : ∀ w ∈ Z, w.re ≤ 1) (g : ℂ → ℂ)
    (hg : ∀ s : ℂ, 1 < s.re → g s = -(LSeries f s - e / (s - 1) + ∑ w ∈ Z, m w / (s - w)))
    (k : ℕ) : ∀ s : ℂ, 1 < s.re → iteratedDeriv k g s = (-1) ^ (k + 1) *
      (LSeries (LSeries.logMul^[k] f) s + k.factorial *
        (- (e / (s - 1) ^ (k + 1)) + ∑ w ∈ Z, m w / (s - w) ^ (k + 1))) := by sorry
