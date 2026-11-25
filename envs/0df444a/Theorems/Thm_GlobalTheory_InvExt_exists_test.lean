-- Prove2me | Theorems.Thm_GlobalTheory_InvExt_exists_test
-- name    : GlobalTheory.InvExt.exists_test
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:14:23.1258+00:00
-- url     : https://prove2.me/theorems/9b692ff6-829d-4cc7-9735-a1d6d8072bdd
-- title:
--   Inv Ext: exists test
-- statement:
--   The Inv Ext construction uses the exists test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsInverseExtensionProperClosure.lean#L147-L167
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsInverseExtensionProperClosure.lean#L147-L167

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

theorem GlobalTheory.InvExt.exists_test (hT : C.HasTests) {p : ℕ} [Fact p.Prime] (α : Sp (OO p) ⟶ C.G.toScheme)
    (a₀ : Sp (PadicAlgCl p) ⟶ C.A.left) (b : Sp (OO p) ⟶ C.P.left) (ha : a₀ ≫ C.a = gPt p ≫ α)
    (hb : gPt p ≫ b = a₀ ≫ (ι[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = α ≫ C.GG.hom) :
    ∃ (y : Sp (OO p) ⟶ C.Z) (τ : C.Test y) (c : Sp (OO p) ⟶ τ.H.left),
      c ≫ τ.H.hom = spMap τ.j ∧ c ≫ τ.f = α ∧ b = (c ≫ (ι[τ.H]).left ≫ τ.f) ≫ C.G.ι := by sorry
