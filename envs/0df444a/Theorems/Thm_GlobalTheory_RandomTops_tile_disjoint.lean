-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_tile_disjoint
-- name    : GlobalTheory.RandomTops.tile_disjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:06.614802+00:00
-- url     : https://prove2.me/theorems/9e26c906-b10b-4a3a-a9af-1bf73dd9ace4
-- title:
--   Random Tops: tile disjoint
-- statement:
--   The Random Tops construction uses the tile disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L327-L329
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L327-L329

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

theorem GlobalTheory.RandomTops.tile_disjoint {r u s s' : ℕ} (h : s ≠ s') : Disjoint (tile r u s) (tile r u s') := by sorry
