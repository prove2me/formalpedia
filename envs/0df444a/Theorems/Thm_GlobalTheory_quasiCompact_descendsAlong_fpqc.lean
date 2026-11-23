-- Prove2me | Theorems.Thm_GlobalTheory_quasiCompact_descendsAlong_fpqc
-- name    : GlobalTheory.quasiCompact_descendsAlong_fpqc
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T10:43:51.73569+00:00
-- url     : https://prove2.me/theorems/9c26a9df-f4cc-405f-a79b-8eeb1b1a552a
-- title:
--   Global Theory: quasi Compact descends Along fpqc
-- statement:
--   The Global Theory construction uses the quasi Compact descends Along fpqc property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomOfFlatQuotientOfAffineKernel.lean#L25-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/IsAffineHomOfFlatQuotientOfAffineKernel.lean#L25-L49

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_UnifUniqSt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_DiscreteValuationRings_FamMod
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_FirstCohomology_DimSplitPf
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsIsoAppTopOfIsPullbackOfSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_IsAffineHomOfFlatQuotientOfAffineKernel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory
universe u
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency.types false

theorem GlobalTheory.quasiCompact_descendsAlong_fpqc :
    MorphismProperty.DescendsAlong (@QuasiCompact : MorphismProperty Scheme.{u})
      (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by sorry
