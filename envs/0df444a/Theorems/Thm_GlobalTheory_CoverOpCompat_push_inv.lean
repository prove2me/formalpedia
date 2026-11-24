-- Prove2me | Theorems.Thm_GlobalTheory_CoverOpCompat_push_inv
-- name    : GlobalTheory.CoverOpCompat.push_inv
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:28:55.248437+00:00
-- url     : https://prove2.me/theorems/7c33d6e1-e019-4b53-92e7-5a2e8be65a86
-- title:
--   Cover Op Compat: push inv
-- statement:
--   The Cover Op Compat construction uses the push inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GroupLawsOnCoverAgreeOnCommonPoints.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/ModuliProofs/GroupLawsOnCoverAgreeOnCommonPoints.lean#L39-L53

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

theorem GlobalTheory.CoverOpCompat.push_inv (h : IsGrpPullback G' G f φ) {T : Scheme.{0}} {ρ : T ⟶ S'} {r : T ⟶ S} (e : r = ρ ≫ f)
    (p : Over.mk ρ ⟶ G') (x : Over.mk r ⟶ G) (hx : x.left = p.left ≫ φ) :
    (x⁻¹).left = (p⁻¹).left ≫ φ := by sorry
