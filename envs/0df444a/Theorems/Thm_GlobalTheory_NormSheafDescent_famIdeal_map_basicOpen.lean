-- Prove2me | Theorems.Thm_GlobalTheory_NormSheafDescent_famIdeal_map_basicOpen
-- name    : GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T20:14:51.35644+00:00
-- url     : https://prove2.me/theorems/5f000e3d-105c-4fb0-9729-41f510a67913
-- title:
--   Norm Sheaf Descent: fam Ideal map basic Open
-- statement:
--   The Norm Sheaf Descent construction uses the fam Ideal map basic Open property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCoeffIdealFamilyMapBasicOpen.lean#L19-L104
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/NormCoeffIdealFamilyMapBasicOpen.lean#L19-L104

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_FamIdeal
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormFormCoefficientIdealMapLocalizationAwayStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_SectionsIsFractionRingStalkImageOfGenericPointStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_CoeffNormFormOfFamilyMemRangeIntegrallyClosedStatement
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_NormCoeffIdealFamilyMapBasicOpen
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits
open GlobalTheory GlobalTheory.NormSheafDescent

theorem GlobalTheory.NormSheafDescent.famIdeal_map_basicOpen : ∀ (Y Z : Scheme.{0}) (π : Y ⟶ Z) [IsFinite π] [IsIntegral Y] [GlobalTheory.IsNormalScheme Z]
    (hK : IsField (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)))
    (hfd : letI := GlobalTheory.NormSheafDescent.fieldK π hK; letI := GlobalTheory.NormSheafDescent.algKL π
      FiniteDimensional (Z.presheaf.stalk (GlobalTheory.NormSheafDescent.genPt π)) Y.functionField)
    (I : Y.IdealSheafData) (U : Z.affineOpens) (f : Γ(Z, U)), (U : Set Z) ⊆ Set.range π →
    (GlobalTheory.NormSheafDescent.famIdeal π hK hfd I U).map (Z.presheaf.map (homOfLE (Z.basicOpen_le f)).op).hom =
      GlobalTheory.NormSheafDescent.famIdeal π hK hfd I (Z.affineBasicOpen f) := by sorry
