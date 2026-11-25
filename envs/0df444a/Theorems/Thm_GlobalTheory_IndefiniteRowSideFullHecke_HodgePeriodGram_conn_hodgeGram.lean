-- Prove2me | Theorems.Thm_GlobalTheory_IndefiniteRowSideFullHecke_HodgePeriodGram_conn_hodgeGram
-- name    : GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.conn_hodgeGram
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T23:44:51.397363+00:00
-- url     : https://prove2.me/theorems/d5207703-733b-48dc-9390-03d4e4ad068f
-- title:
--   Hodge Period Gram: conn hodge Gram
-- statement:
--   The Hodge Period Gram construction uses the conn hodge Gram property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/HodgePeriodGram.lean#L101-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/BlockTheory/DivisorBase/HodgePeriodGram.lean#L101-L120

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

theorem GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.conn_hodgeGram {rk : ℕ} (ha : a ≤ n) {τ₀ : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ}
    {B : Fin a → Matrix (Fin g) (Fin g) ℤ} (h : _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.IsPeriodChart rk τ₀ B) {z : Fin n → ℂ}
    (hz : z ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.polydisc n 1) (ξ : Fin n → ℂ) :
    _root_.GlobalTheory.HermFrame.conn (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ =
      (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B z)⁻¹ * _root_.GlobalTheory.HermFrame.mdel (_root_.GlobalTheory.IndefiniteRowSideFullHecke.HodgePeriodGram.hodgeGram ha τ₀ B) z ξ := by sorry
