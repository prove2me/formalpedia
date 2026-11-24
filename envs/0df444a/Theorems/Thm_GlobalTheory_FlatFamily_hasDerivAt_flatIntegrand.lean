-- Prove2me | Theorems.Thm_GlobalTheory_FlatFamily_hasDerivAt_flatIntegrand
-- name    : GlobalTheory.FlatFamily.hasDerivAt_flatIntegrand
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T13:32:51.695468+00:00
-- url     : https://prove2.me/theorems/de5e2694-f1de-414b-a329-73eb0fd96b36
-- title:
--   Flat Family: has Deriv At flat Integrand
-- statement:
--   The Flat Family construction uses the has Deriv At flat Integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFamilyZetaConvergenceHolomorphy.lean#L43-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFamilyZetaConvergenceHolomorphy.lean#L43-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_FlatFamilyZetaConvergenceHolomorphy
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open GlobalTheory GlobalTheory.FlatFamily
open GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
variable {X : Type} [MeasurableSpace X]
omit [MeasurableSpace X]

theorem GlobalTheory.FlatFamily.hasDerivAt_flatIntegrand (f : X → ℂ) {a : X → ℝ} (ha : ∀ x, 0 < a x) (s₀ s : ℂ) (x : X) :
    HasDerivAt (fun z => flatIntegrand f a s₀ z x)
      (flatIntegrand f a s₀ s x * ((Real.log (a x) : ℝ) : ℂ)) s := by sorry
