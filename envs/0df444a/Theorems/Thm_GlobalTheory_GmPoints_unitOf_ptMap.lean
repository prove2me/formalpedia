-- Prove2me | Theorems.Thm_GlobalTheory_GmPoints_unitOf_ptMap
-- name    : GlobalTheory.GmPoints.unitOf_ptMap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T15:16:51.389927+00:00
-- url     : https://prove2.me/theorems/995d3c7b-85db-4898-9abe-c1c6b89e1061
-- title:
--   Gm Points: unit Of pt Map
-- statement:
--   The Gm Points construction uses the unit Of pt Map property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitOfBijectiveMulNatural.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/JetHarmonics/UnitOfBijectiveMulNatural.lean#L74-L79

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_PlaceDivisors_ThmASt
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_RosatiAdj
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_ExtensionDescent_GlobalSectionsRankAlgClosed
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_ValCalc
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsSplitTorusPointsMulEquiv
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_JetHarmonics_UnitOfBijectiveMulNatural
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open GlobalTheory.GmPoints
variable {O : Type} [CommRing O] {R : Type} [CommRing R] [Algebra O R]

theorem GlobalTheory.GmPoints.unitOf_ptMap {R' : Type} [CommRing R'] [Algebra O R'] (φ : R →ₐ[O] R')
    (w : specO O R ⟶ Gm (Spec (CommRingCat.of O))) :
    (unitOf (ptMap φ ≫ w) : R') = φ (unitOf w : R) := by sorry
