-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_dotProduct_gram_pos_of_rat
-- name    : GlobalTheory.ClassMin.dotProduct_gram_pos_of_rat
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:07:44.280644+00:00
-- url     : https://prove2.me/theorems/62402538-ee8a-4c6d-b5e9-6e8e7c19d058
-- title:
--   Class Min: dot Product gram pos of rat
-- statement:
--   The Class Min construction uses the dot Product gram pos of rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L198-L220
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L198-L220

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
variable {X : Type*} [AddCommGroup X] {ι : Type*} {Q : QuadraticMap ℤ X ℝ}

theorem GlobalTheory.ClassMin.dotProduct_gram_pos_of_rat [Fintype ι] (hQ : Q.PosDef) (e : Module.Basis ι ℤ X) {x : ι → ℚ}
    (hx : x ≠ 0) : 0 < (fun i => (x i : ℝ)) ⬝ᵥ (gram Q e *ᵥ fun i => (x i : ℝ)) := by sorry
