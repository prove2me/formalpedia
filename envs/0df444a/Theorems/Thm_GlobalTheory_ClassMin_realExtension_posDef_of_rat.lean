-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_realExtension_posDef_of_rat
-- name    : GlobalTheory.ClassMin.realExtension_posDef_of_rat
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T11:13:12.920896+00:00
-- url     : https://prove2.me/theorems/de056f39-1641-46d3-85b9-1a56539e419c
-- title:
--   Class Min: real Extension pos Def of rat
-- statement:
--   The Class Min construction uses the real Extension pos Def of rat property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L237-L257
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L237-L257

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

theorem GlobalTheory.ClassMin.realExtension_posDef_of_rat [Module.Free ℤ X] [Module.Finite ℤ X] (hQ : Q.PosDef)
    (hr : ∀ x y, ∃ q : ℚ, polar Q x y = q) : (realExtension Q).PosDef := by sorry
