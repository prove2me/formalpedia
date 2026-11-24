-- Prove2me | Theorems.Thm_GlobalTheory_ClassMin_realExtension_ofIntBilin_posDef
-- name    : GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T06:06:36.112918+00:00
-- url     : https://prove2.me/theorems/0db320ae-8b42-4503-8ab8-e9ef4e112b4e
-- title:
--   Class Min: real Extension of Int Bilin pos Def
-- statement:
--   The Class Min construction uses the real Extension of Int Bilin pos Def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L273-L280
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FoundationProofs/EqOfIsMinInClassTwoOfSameClassFour.lean#L273-L280

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

theorem GlobalTheory.ClassMin.realExtension_ofIntBilin_posDef [Module.Free ℤ X] [Module.Finite ℤ X]
    {β : LinearMap.BilinForm ℤ X} (hβ : ∀ x y, β x y = β y x) (hpos : ∀ x, x ≠ 0 → 0 < β x x) :
    (realExtension (ofIntBilin β)).PosDef := by sorry
