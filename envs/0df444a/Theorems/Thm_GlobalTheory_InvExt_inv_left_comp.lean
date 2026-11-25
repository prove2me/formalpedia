-- Prove2me | Theorems.Thm_GlobalTheory_InvExt_inv_left_comp
-- name    : GlobalTheory.InvExt.inv_left_comp
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:14:56.973366+00:00
-- url     : https://prove2.me/theorems/161864fd-d756-42df-8b26-94347123475e
-- title:
--   Inv Ext: inv left comp
-- statement:
--   The Inv Ext construction uses the inv left comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsInverseExtensionProperClosure.lean#L15-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsInverseExtensionProperClosure.lean#L15-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsInverseExtensionProperClosure
import Theorems.Thm_P2M_UpperTheory_Reformulated_B_Qk17_isPrecomplete_finite_module__f12f74bf6019

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
open GlobalTheory.ZJ
open GlobalTheory GlobalTheory.InvExt

theorem GlobalTheory.InvExt.inv_left_comp {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (ι[G']).left ≫ φ = φ ≫ (ι[G]).left := by sorry
