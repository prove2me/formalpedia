-- Prove2me | Theorems.Thm_GlobalTheory_FlatFamily_flatIntegrand_rebase
-- name    : GlobalTheory.FlatFamily.flatIntegrand_rebase
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T18:42:52.604779+00:00
-- url     : https://prove2.me/theorems/e1a948a4-0242-424e-8b1b-152432ae8f82
-- title:
--   Flat Family: flat Integrand rebase
-- statement:
--   The Flat Family construction uses the flat Integrand rebase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFamilyZetaConvergenceHolomorphy.lean#L14-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/FlatFamilyZetaConvergenceHolomorphy.lean#L14-L20

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

theorem GlobalTheory.FlatFamily.flatIntegrand_rebase (f : X → ℂ) {a : X → ℝ} (ha : ∀ x, 0 < a x) (s₀ s₁ s : ℂ) (x : X) :
    flatIntegrand f a s₀ s x = flatIntegrand f a s₀ s₁ x * ((a x : ℝ) : ℂ) ^ (s - s₁) := by sorry
