-- Prove2me | Theorems.Thm_GlobalTheory_T_normCoefficientIdealFamily_eq_top_of_disjoint
-- name    : GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:36:23.845411+00:00
-- url     : https://prove2.me/theorems/b92cdbc5-93e0-4a4e-96dd-8308850f2430
-- title:
--   T: norm Coefficient Ideal Family eq top of disjoint
-- statement:
--   The T construction uses the norm Coefficient Ideal Family eq top of disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCoefficientIdealFamilyEqTopOfDisjointStatement.lean#L9-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCoefficientIdealFamilyEqTopOfDisjointStatement.lean#L9-L15

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoefficientIdealFamilyEqTopOfDisjoint
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoefficientIdealFamilyEqTopOfDisjointStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.normCoefficientIdealFamily_eq_top_of_disjoint : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens), (∀ y ∈ I.support, π y ∉ (U : Set Z)) →
    GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U = ⊤ := by sorry
