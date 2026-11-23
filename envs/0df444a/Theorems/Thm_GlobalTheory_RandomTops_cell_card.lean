-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_cell_card
-- name    : GlobalTheory.RandomTops.cell_card
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:43:16.244834+00:00
-- url     : https://prove2.me/theorems/7f155bef-6da2-437f-92ab-ba60abd9f92d
-- title:
--   Random Tops: cell card
-- statement:
--   The Random Tops construction uses the cell card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L310-L314
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L310-L314

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

theorem GlobalTheory.RandomTops.cell_card {r u s c : ℕ} (hc : 1 ≤ c) : (cell r u s c).card = u := by sorry
