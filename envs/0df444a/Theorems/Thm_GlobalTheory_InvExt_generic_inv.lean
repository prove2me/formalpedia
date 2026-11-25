-- Prove2me | Theorems.Thm_GlobalTheory_InvExt_generic_inv
-- name    : GlobalTheory.InvExt.generic_inv
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:14:14.544413+00:00
-- url     : https://prove2.me/theorems/ee12808e-24a4-43e7-857a-735ce30a7037
-- title:
--   Inv Ext: generic inv
-- statement:
--   The Inv Ext construction uses the generic inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsInverseExtensionProperClosure.lean#L49-L76
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsInverseExtensionProperClosure.lean#L49-L76

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

theorem GlobalTheory.InvExt.generic_inv {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (c : Sp (OO p) ⟶ τ.H.left) (hc : c ≫ τ.H.hom = spMap τ.j) (a₀ : Sp (PadicAlgCl p) ⟶ C.A.left)
    (ha : a₀ ≫ C.a = gPt p ≫ c ≫ τ.f) :
    gPt p ≫ c ≫ (ι[τ.H]).left ≫ τ.f = a₀ ≫ (ι[C.A]).left ≫ C.a := by sorry
