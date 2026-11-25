-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HodgePeriodGram_im_period
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:20.570851+00:00
-- url     : https://prove2.me/theorems/902fe51c-17ae-4696-8c9c-e3e096c75f33
-- title:
--   Hodge Period Gram: im period
-- statement:
--   The Hodge Period Gram construction uses the im period property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/HodgePeriodGram.lean#L82-L95
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/HodgePeriodGram.lean#L82-L95

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Divisors_ExtFormAdjEqNegSecondForm
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_DivisorBase_HodgePeriodGram
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Complex Filter Topology
open scoped ComplexOrder
noncomputable section
open GlobalTheory GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram
open GlobalTheory.HermFrame
variable {n a g : ℕ}
open Matrix Complex Filter Topology
open scoped ComplexOrder
variable {n a g : ℕ}

theorem GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.im_period (ha : a ≤ n) (τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ)
    (B : Fin a → Matrix (Fin g) (Fin g) ℤ) (z : Fin n → ℂ) (L : Fin a → ℂ)
    (hL : ∀ i, exp (L i) = z (Fin.castLE ha i)) :
    (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.period τ₀ B z L).map Complex.im = _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.imPeriod ha τ₀ B z := by sorry
