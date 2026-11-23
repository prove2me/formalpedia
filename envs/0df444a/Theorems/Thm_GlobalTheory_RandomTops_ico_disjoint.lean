-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ico_disjoint
-- name    : GlobalTheory.RandomTops.ico_disjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:23.615804+00:00
-- url     : https://prove2.me/theorems/758095c3-05b2-4ab4-a0d2-93bd4fccfc7c
-- title:
--   Random Tops: ico disjoint
-- statement:
--   The Random Tops construction uses the ico disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L316-L325
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L316-L325

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

theorem GlobalTheory.RandomTops.ico_disjoint {a m i j : ℕ} (hij : i ≠ j) :
    Disjoint (Finset.Ico (a + i * m) (a + (i + 1) * m)) (Finset.Ico (a + j * m) (a + (j + 1) * m)) := by sorry
