-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_val_eq_of_affine
-- name    : GlobalTheory.TorusConst.val_eq_of_affine
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:10:08.524489+00:00
-- url     : https://prove2.me/theorems/a6a61328-c8a9-4f98-ba77-1759caadbd3a
-- title:
--   Torus Const: val eq of affine
-- statement:
--   The Torus Const construction uses the val eq of affine property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L234-L272
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L234-L272

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

theorem GlobalTheory.TorusConst.val_eq_of_affine {A : Type} [Field A] [Algebra K A] {F G : sp K A[X] ⟶ B} (h : Glue F G)
    (V : B.left.Opens) (hV : IsAffineOpen V) (hF : ∀ q, F.left q ∈ V) (hG : ∀ q, G.left q ∈ V)
    (x y : A) : val F (AlgHom.id K A) x = val F (AlgHom.id K A) y := by sorry
