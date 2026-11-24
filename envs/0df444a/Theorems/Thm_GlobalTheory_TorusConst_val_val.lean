-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_val_val
-- name    : GlobalTheory.TorusConst.val_val
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:09:42.933796+00:00
-- url     : https://prove2.me/theorems/0a18dbf8-26cc-4841-8ce7-d83deb2f09e7
-- title:
--   Torus Const: val val
-- statement:
--   The Torus Const construction uses the val val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L164-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L164-L167

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

theorem GlobalTheory.TorusConst.val_val {R S A : Type} [CommRing R] [Algebra K R] [CommRing S] [Algebra K S] [CommRing A]
    [Algebra K A] (F : sp K R[X] ⟶ B) (c : R →ₐ[K] S[X]) (x : S[X]) (d : S →ₐ[K] A) (y : A) :
    val (val F c x) d y = val F ((aevalTower d y).comp c) (aevalTower d y x) := by sorry
