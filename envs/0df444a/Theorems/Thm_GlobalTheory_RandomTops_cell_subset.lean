-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_cell_subset
-- name    : GlobalTheory.RandomTops.cell_subset
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:08.866147+00:00
-- url     : https://prove2.me/theorems/0bcf8a8a-5a6c-4d6d-b81d-11a1c7be1fd1
-- title:
--   Random Tops: cell subset
-- statement:
--   The Random Tops construction uses the cell subset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L304-L308
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L304-L308

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

theorem GlobalTheory.RandomTops.cell_subset {r u s c : ℕ} (hc : c ≤ 6 * r + 1) : cell r u s c ⊆ tile r u s := by sorry
