-- Prove2me | Theorems.Thm_GlobalTheory_PartialIntegral_eventually_invariant
-- name    : GlobalTheory.PartialIntegral.eventually_invariant
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:41:13.480695+00:00
-- url     : https://prove2.me/theorems/d53fb69e-c1a9-4793-9972-158c0cd84fff
-- title:
--   Partial Integral: eventually invariant
-- statement:
--   The Partial Integral construction uses the eventually invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LocallyConstantPartial.lean#L108-L126
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LocallyConstantPartial.lean#L108-L126

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LocallyConstantPartial
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped SchwartzMap ContDiff
open GlobalTheory GlobalTheory.PartialIntegral
variable {Y B W : Type} [AddCommGroup Y] [TopologicalSpace Y] [IsTopologicalAddGroup Y] [T2Space Y] [MeasurableSpace Y]
  [BorelSpace Y] [TopologicalSpace B] [T2Space B] [AddCommGroup W] [TopologicalSpace W] [IsTopologicalAddGroup W]
  (ν : Measure Y) [ν.IsAddHaarMeasure]

theorem GlobalTheory.PartialIntegral.eventually_invariant {g : W → ℂ} (h1 : IsLocallyConstant g) (h2 : HasCompactSupport g) :
    ∀ᶠ u in 𝓝 (0 : W), ∀ x, g (x + u) = g x := by sorry
