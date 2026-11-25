-- Prove2me | Theorems.Thm_GlobalTheory_Lin_Repulsion_exists_list
-- name    : GlobalTheory.Lin.Repulsion.exists_list
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T18:06:44.711494+00:00
-- url     : https://prove2.me/theorems/e31657f1-32f8-4f11-9774-d24946c4283e
-- title:
--   Repulsion: exists list
-- statement:
--   The Repulsion construction uses the exists list property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L164-L202
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/Repulsion.lean#L164-L202

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

theorem GlobalTheory.Lin.Repulsion.exists_list : ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (t L : ℝ),
    Real.log (q * (|t| + 2)) ≤ L → ∃ W : Multiset ℂ,
      (∀ w : ℂ, ‖w - (2 + t * I)‖ ≤ 3 → w ≠ 1 → LFunction χ w = 0 → W.count w = ord χ w) ∧
      (W.card : ℝ) ≤ C * L ∧ ∀ k : ℕ,
        (derSeries (fun n : ℕ => χ (n : ZMod q)) k (2 + t * I)).re + (powSum W t (k + 1)).re ≤
          (if χ = 1 then 1 / ((2 : ℂ) + t * I - 1) ^ (k + 1) else 0).re + 2 * C * L / 2 ^ (k + 1) := by sorry
