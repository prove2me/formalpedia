-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_exists_poly
-- name    : GlobalTheory.TorusConst.exists_poly
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:36.111444+00:00
-- url     : https://prove2.me/theorems/1264519b-1523-4e97-a412-b9b1a83bf64c
-- title:
--   Torus Const: exists poly
-- statement:
--   The Torus Const construction uses the exists poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L176-L206
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L176-L206

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

theorem GlobalTheory.TorusConst.exists_poly {R L : Type} [CommRing R] [Algebra K R] [Field L] [Algebra K L]
    (F : sp K R[X] ⟶ B) (V : B.left.Opens) (e : R →ₐ[K] L) (he : Function.Surjective e)
    (hF : ∀ q, (val F (CAlgHom.comp e) (X : L[X])).left q ∈ V) :
    ∃ a : R[X], a.map (e : R →+* L) = 1 ∧ ∀ (A : Type) [Field A] [Algebra K A] (c : R →ₐ[K] A) (x : A) (q),
      (val F c x).left q ∉ V → eval₂ (c : R →+* A) x a = 0 := by sorry
