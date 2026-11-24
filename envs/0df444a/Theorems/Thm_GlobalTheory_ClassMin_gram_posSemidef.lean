-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_gram_posSemidef
-- name    : GlobalTheory.ClassMin.gram_posSemidef
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T11:11:08.129434+00:00
-- url     : https://prove2.me/theorems/2705a7ec-dac8-42c1-9283-bc4d26e31931
-- title:
--   Class Min: gram pos Semidef
-- statement:
--   The Class Min construction uses the gram pos Semidef property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L222-L235
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L222-L235

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

theorem GlobalTheory.ClassMin.gram_posSemidef [Finite ι] (hQ : Q.PosDef) (e : Module.Basis ι ℤ X) :
    (gram Q e).PosSemidef := by sorry
