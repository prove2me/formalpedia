-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_val_twist
-- name    : GlobalTheory.TorusConst.val_twist
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:29.958121+00:00
-- url     : https://prove2.me/theorems/ee1b6683-1e25-4acf-afc1-ab5b42338749
-- title:
--   Torus Const: val twist
-- statement:
--   The Torus Const construction uses the val twist property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L280-L287
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L280-L287

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

theorem GlobalTheory.TorusConst.val_twist (b : sp K L[X] ⟶ B) (i : L →ₐ[K] R) (s : R) {A : Type} [CommRing A] [Algebra K A]
    (c : R →ₐ[K] A) (x : A) :
    val (twist b i s) c x = val b (c.comp i) (c s * x) * (val b (c.comp i) x)⁻¹ := by sorry
