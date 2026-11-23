-- Prove2me | Theorems.Thm_GlobalTheory_CoverOpCompat_push_mul
-- name    : GlobalTheory.CoverOpCompat.push_mul
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-11-23T11:26:50.177563+00:00
-- url     : https://prove2.me/theorems/110c0b38-48e3-4b90-a916-4ae502f1d7c2
-- title:
--   Cover Op Compat: push mul
-- statement:
--   The Cover Op Compat construction uses the push mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GroupLawsOnCoverAgreeOnCommonPoints.lean#L33-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GroupLawsOnCoverAgreeOnCommonPoints.lean#L33-L37

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_ExistsUniqueHom
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ModuliSpaces_FiniteHomogeneousInf
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_BCTools
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_ModuliProofs_GroupLawsOnCoverAgreeOnCommonPoints
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM
open GlobalTheory GlobalTheory.CoverOpCompat
variable {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

theorem GlobalTheory.CoverOpCompat.push_mul (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p q : Over.mk ρ ⟶ G') (x y : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) (hy : y.left = q.left ≫ φ) :
    (x * y).left = (p * q).left ≫ φ := by sorry
