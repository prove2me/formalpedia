-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_prod_alternate
-- name    : GlobalTheory.RandomTops.prod_alternate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:44:42.705549+00:00
-- url     : https://prove2.me/theorems/fa5b432f-3b92-4e07-9399-6a5e7cfdef29
-- title:
--   Random Tops: prod alternate
-- statement:
--   The Random Tops construction uses the prod alternate property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L375-L384
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L375-L384

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

theorem GlobalTheory.RandomTops.prod_alternate (a b : ℝ) (m : ℕ) :
    ∏ c ∈ Finset.range (2 * m + 1), (if Even c then a else b) = a ^ (m + 1) * b ^ m := by sorry
