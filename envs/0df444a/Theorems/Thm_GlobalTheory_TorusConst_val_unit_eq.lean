-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_val_unit_eq
-- name    : GlobalTheory.TorusConst.val_unit_eq
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:14.761709+00:00
-- url     : https://prove2.me/theorems/a19d311d-d59b-4206-af7a-0f298b8bdb36
-- title:
--   Torus Const: val unit eq
-- statement:
--   The Torus Const construction uses the val unit eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L289-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L289-L333

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_SplitTorusHomProperTrivialField
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_SplitTorusToAbelianVarietyConst
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.TorusConst
open Polynomial TorusToProper
variable {K : Type} [Field K] {B : Over (Spec (CommRingCat.of K))}
variable [GrpObj B] {L R : Type} [Field L] [Algebra K L] [CommRing R] [Algebra K R]

theorem GlobalTheory.TorusConst.val_unit_eq [IsSeparated B.hom] [IsDomain R] {b b' : sp K L[X] ⟶ B} (h : Glue b b')
    (i : L →ₐ[K] R) (t : Rˣ) (e : R →ₐ[K] L) (he : Function.Surjective e) (het : e t = 1) :
    val b i (t : R) = val b i 1 := by sorry
