-- Prove2me | Theorems.Thm_GlobalTheory_InvExt_special_inv
-- name    : GlobalTheory.InvExt.special_inv
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:14:09.142469+00:00
-- url     : https://prove2.me/theorems/57e3c58a-3f0e-4a4b-aa80-0f6ba49b8cf0
-- title:
--   Inv Ext: special inv
-- statement:
--   The Inv Ext construction uses the special inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsInverseExtensionProperClosure.lean#L125-L145
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsInverseExtensionProperClosure.lean#L125-L145

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsInverseExtensionProperClosure
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
variable (C : Core)
variable {C}

theorem GlobalTheory.InvExt.special_inv (hF : C.FibLaw) {p : ℕ} [Fact p.Prime] {y y' : Sp (OO p) ⟶ C.Z}
    (τ : C.Test y) (τ' : C.Test y')
    (c : Sp (OO p) ⟶ τ.H.left) (hc : c ≫ τ.H.hom = spMap τ.j)
    (c' : Sp (OO p) ⟶ τ'.H.left) (hc' : c' ≫ τ'.H.hom = spMap τ'.j)
    (h : (c ≫ τ.f) (cPt p) = (c' ≫ τ'.f) (cPt p)) :
    (c ≫ (ι[τ.H]).left ≫ τ.f) (cPt p) = (c' ≫ (ι[τ'.H]).left ≫ τ'.f) (cPt p) := by sorry
