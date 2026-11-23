-- Prove2me | Theorems.Thm_GlobalTheory_FlatQuotient_epi_tensorHom
-- name    : GlobalTheory.FlatQuotient.epi_tensorHom
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T07:36:13.782107+00:00
-- url     : https://prove2.me/theorems/57699935-dec0-47ff-8094-1104d31d9c01
-- title:
--   Flat Quotient: epi tensor Hom
-- statement:
--   The Flat Quotient construction uses the epi tensor Hom property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatQuotientIsoOfSameKernel.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatQuotientIsoOfSameKernel.lean#L69-L79

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

theorem GlobalTheory.FlatQuotient.epi_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y')
    [hf : Flat f.left] [hf' : Surjective f.left] [hg : Flat g.left] [hg' : Surjective g.left] :
    Epi (f ⊗ₘ g) := by sorry
