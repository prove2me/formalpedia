-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_tiles_le
-- name    : GlobalTheory.RandomTops.tiles_le
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:16.85948+00:00
-- url     : https://prove2.me/theorems/7a26b5b5-b931-4c07-96f9-03e6913eadef
-- title:
--   Random Tops: tiles le
-- statement:
--   The Random Tops construction uses the tiles le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L479-L582
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L479-L582

import Mathlib
import Definitions.Def_Formalism_SubspaceCounting_GoodOrbitIntervalTileCondition
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_GlobalInterpolation_ChoiceOfTops
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset Formalism.G0
open GlobalTheory GlobalTheory.RandomTops
variable {δ : ℝ}

theorem GlobalTheory.RandomTops.tiles_le (h0 : 0 ≤ δ) (h1 : δ ≤ 1) {n r u M₀ i₀ : ℕ} (hu : 1 ≤ u)
    (hn : (M₀ + 1) * ((6 * r + 1) * u) ≤ n) :
    ex δ ((Finset.range n).erase i₀) (fun U => ind (¬ CondTiles n (insert i₀ U) r u M₀)) ≤
      n * (1 - markedBound δ r u) ^ M₀ := by sorry
