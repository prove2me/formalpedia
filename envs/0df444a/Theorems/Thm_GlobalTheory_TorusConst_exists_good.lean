-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_exists_good
-- name    : GlobalTheory.TorusConst.exists_good
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:09:38.075788+00:00
-- url     : https://prove2.me/theorems/861890ff-e05b-4ab9-be2c-24ca3be841da
-- title:
--   Torus Const: exists good
-- statement:
--   The Torus Const construction uses the exists good property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L208-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L208-L232

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

theorem GlobalTheory.TorusConst.exists_good {R L : Type} [CommRing R] [Algebra K R] [Field L] [Algebra K L]
    {F G : sp K R[X] ⟶ B} (h : Glue F G) (V : B.left.Opens) (e : R →ₐ[K] L)
    (he : Function.Surjective e)
    (hF : ∀ q, (val F (CAlgHom.comp e) (X : L[X])).left q ∈ V)
    (hG : ∀ q, (val G (CAlgHom.comp e) (X : L[X])).left q ∈ V) :
    ∃ g : R, e g ≠ 0 ∧ ∀ (A : Type) [Field A] [Algebra K A] (c : R →ₐ[K] A), c g ≠ 0 →
      ∀ q, (val F (CAlgHom.comp c) (X : A[X])).left q ∈ V := by sorry
