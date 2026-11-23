-- Prove2me | Theorems.Thm_GlobalTheory_FlatQuotient_epi_of_flat_surjective
-- name    : GlobalTheory.FlatQuotient.epi_of_flat_surjective
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T07:28:42.374511+00:00
-- url     : https://prove2.me/theorems/95ff8510-c109-4dee-a32c-ba4d1bce7243
-- title:
--   Flat Quotient: epi of flat surjective
-- statement:
--   The Flat Quotient construction uses the epi of flat surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatQuotientIsoOfSameKernel.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatQuotientIsoOfSameKernel.lean#L19-L22

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_DegExp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_FlatQuotientIsoOfSameKernel
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
open GlobalTheory.FlatQuotient
variable {S : Scheme.{0}}
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
variable {S : Scheme.{0}}

theorem GlobalTheory.FlatQuotient.epi_of_flat_surjective {X Y : Over S} (f : X ⟶ Y) [Flat f.left] [Surjective f.left] :
    Epi f := by sorry
