-- Prove2me | Theorems.Thm_GlobalTheory_FlatQuotient_comp_eq_of_kills_kernel
-- name    : GlobalTheory.FlatQuotient.comp_eq_of_kills_kernel
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T13:32:36.11495+00:00
-- url     : https://prove2.me/theorems/55d6fafe-5540-44c1-a2ad-d0e302cd952b
-- title:
--   Flat Quotient: comp eq of kills kernel
-- statement:
--   The Flat Quotient construction uses the comp eq of kills kernel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatQuotientIsoOfSameKernel.lean#L86-L97
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AbelianSchemeLawProofs/FlatQuotientIsoOfSameKernel.lean#L86-L97

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

theorem GlobalTheory.FlatQuotient.comp_eq_of_kills_kernel {G B B' T : Over S} [GrpObj G] [GrpObj B] [GrpObj B']
    (q : G ⟶ B) (i : T ⟶ G) (f : G ⟶ B') [IsMonHom q] [IsMonHom f]
    (hker : IsPullback i (toUnit _) q (η[B])) (hf : i ≫ f = toUnit _ ≫ η[B'])
    {Z : Over S} (g g' : Z ⟶ G) (h : g ≫ q = g' ≫ q) : g ≫ f = g' ≫ f := by sorry
