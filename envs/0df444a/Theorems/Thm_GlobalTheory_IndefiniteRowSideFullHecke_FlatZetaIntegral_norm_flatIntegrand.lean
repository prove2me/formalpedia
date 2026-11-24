-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_FlatZetaIntegral_norm_flatIntegrand
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.norm_flatIntegrand
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T17:14:06.315442+00:00
-- url     : https://prove2.me/theorems/eaed51e1-4ed0-44cc-aa87-feeced75c56c
-- title:
--   Flat Zeta Integral: norm flat Integrand
-- statement:
--   The Flat Zeta Integral construction uses the norm flat Integrand property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/FlatZetaIntegral.lean#L36-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/TorsionBlocks/FlatZetaIntegral.lean#L36-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TorsionBlocks_FlatZetaIntegral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Set
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral
variable {X : Type} [MeasurableSpace X]
omit [MeasurableSpace X]

theorem GlobalTheory.IndefiniteRowSideFullHecke.FlatZetaIntegral.norm_flatIntegrand (f : X → ℂ) {a : X → ℝ} (s₀ s : ℂ) {x : X} (hx : 0 < a x) :
    ‖flatIntegrand f a s₀ s x‖ = ‖f x‖ * a x ^ (s.re - s₀.re) := by sorry
