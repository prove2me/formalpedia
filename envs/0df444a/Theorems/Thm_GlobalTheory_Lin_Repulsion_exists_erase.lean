-- Prove2me | Theorems.Thm_GlobalTheory_Lin_Repulsion_exists_erase
-- name    : GlobalTheory.Lin.Repulsion.exists_erase
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T18:06:30.522752+00:00
-- url     : https://prove2.me/theorems/3d421719-172c-4578-94b3-35a8c2cad16a
-- title:
--   Repulsion: exists erase
-- statement:
--   The Repulsion construction uses the exists erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L204-L230
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L204-L230

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_GlobalTwisting_ZerosDisc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_IteratedDerivLogDerivDirichletLViaNearbyZeros
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_SumIccThreeQuartersPowLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_Repulsion
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
open GlobalTheory GlobalTheory.Lin GlobalTheory.Lin.Repulsion

theorem GlobalTheory.Lin.Repulsion.exists_erase {β : ℝ} (hβ : β < 1) (hβ' : 1 / 2 ≤ β) (W : Multiset ℂ) (t : ℝ)
    (h : ‖(β : ℂ) - (2 + t * I)‖ ≤ 3 → (β : ℂ) ∈ W) : ∃ W' : Multiset ℂ, W'.card ≤ W.card ∧
      (∀ w ∈ W, w ≠ β ∨ 2 ≤ W.count w → w ∈ W') ∧ ∀ j : ℕ,
        (powSum W' t j).re + (1 / ((2 : ℂ) + t * I - 1) ^ j).re ≤
          (powSum W t j).re + j * (1 - β) + 1 / 2 ^ j := by sorry
