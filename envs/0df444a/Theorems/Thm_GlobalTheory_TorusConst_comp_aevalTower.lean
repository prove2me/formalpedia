-- Prove2me | Theorems.Thm_GlobalTheory_TorusConst_comp_aevalTower
-- name    : GlobalTheory.TorusConst.comp_aevalTower
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T12:06:11.808805+00:00
-- url     : https://prove2.me/theorems/80e489af-7e00-47d4-8feb-87c4c22bceeb
-- title:
--   Torus Const: comp aeval Tower
-- statement:
--   The Torus Const construction uses the comp aeval Tower property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L144-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/SplitTorusToAbelianVarietyConst.lean#L144-L150

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

theorem GlobalTheory.TorusConst.comp_aevalTower {R A A' : Type} [CommRing R] [Algebra K R] [CommRing A] [Algebra K A]
    [CommRing A'] [Algebra K A'] (g : A →ₐ[K] A') (c : R →ₐ[K] A) (x : A) :
    g.comp (aevalTower c x) = aevalTower (g.comp c) (g x) := by sorry
