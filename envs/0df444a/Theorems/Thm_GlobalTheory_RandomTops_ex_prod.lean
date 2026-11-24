-- Prove2me | Theorems.Thm_GlobalTheory_RandomTops_ex_prod
-- name    : GlobalTheory.RandomTops.ex_prod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T05:07:17.63668+00:00
-- url     : https://prove2.me/theorems/44bbe653-93b1-4fbf-b183-82e1b7a2db89
-- title:
--   Random Tops: ex prod
-- statement:
--   The Random Tops construction uses the ex prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L145-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/GlobalInterpolation/ChoiceOfTops.lean#L145-L177

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

theorem GlobalTheory.RandomTops.ex_prod {ι : Type*} (J : Finset ι) (A : ι → Finset ℕ) (g : ι → Finset ℕ → ℝ)
    (hd : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (A i) (A j)) (S : Finset ℕ)
    (hS : ∀ j ∈ J, A j ⊆ S) :
    ex δ S (fun T => ∏ j ∈ J, g j (T ∩ A j)) = ∏ j ∈ J, ex δ (A j) (g j) := by sorry
