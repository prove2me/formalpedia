-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_finite_affine_sublevel
-- name    : GlobalTheory.ClassMin.finite_affine_sublevel
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:36.418386+00:00
-- url     : https://prove2.me/theorems/e3d872b5-1baa-410b-b8ff-961719c34ea8
-- title:
--   Class Min: finite affine sublevel
-- statement:
--   The Class Min construction uses the finite affine sublevel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L300-L336
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L300-L336

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
variable {X : Type*} [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X]
  {Q : QuadraticMap ℤ X ℝ}

theorem GlobalTheory.ClassMin.finite_affine_sublevel (hQ : (realExtension Q).PosDef) {t : ℝ} (ht : 0 < t) (ν : X →+ ℝ)
    (r : ℝ) : {x | t * Q x + ν x ≤ r}.Finite := by sorry
