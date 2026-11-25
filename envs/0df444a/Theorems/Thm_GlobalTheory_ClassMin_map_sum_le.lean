-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_map_sum_le
-- name    : GlobalTheory.ClassMin.map_sum_le
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T11:58:49.054782+00:00
-- url     : https://prove2.me/theorems/5d154562-ce38-479d-b820-ec1975e05e7e
-- title:
--   Class Min: map sum le
-- statement:
--   The Class Min construction uses the map sum le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L93-L106
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L93-L106

import Mathlib
import Definitions.Def_ReciprocityTheory_ReducedBases_LatDefs
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ThetaMetrics_ExistsEventuallyNormRiemannThetaTermLe
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FoundationProofs_EqOfIsMinInClassTwoOfSameClassFour
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.ClassMin
open QuadraticMap Matrix Filter
open scoped TensorProduct
variable {X : Type*} [AddCommGroup X] {Q : QuadraticMap ℤ X ℝ}

theorem GlobalTheory.ClassMin.map_sum_le (hQ : ∀ x, 0 ≤ Q x) {ι : Type*} (s : Finset ι) (v : ι → X) :
    Q (∑ i ∈ s, v i) ≤ s.card * ∑ i ∈ s, Q (v i) := by sorry
