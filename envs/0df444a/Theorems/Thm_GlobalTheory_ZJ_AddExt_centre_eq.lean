-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_AddExt_centre_eq
-- name    : GlobalTheory.ZJ.AddExt.centre_eq
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:16:49.745585+00:00
-- url     : https://prove2.me/theorems/93ce206f-819a-4bc6-a257-d7e054307185
-- title:
--   Add Ext: centre eq
-- statement:
--   The Add Ext construction uses the centre eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddExtension.lean#L233-L264
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddExtension.lean#L233-L264

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Degenerations_IsNormalSchemeSp
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_SabPull
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_ShimuraVarieties_IsOpenOfMemIrreducibleComponentsOfFinite
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_FiniteOfIsClosedOfFiniteInterClosedPoints
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsAddExtension
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
open GlobalTheory GlobalTheory.ZJ GlobalTheory.ZJ.AddExt

theorem GlobalTheory.ZJ.AddExt.centre_eq (C : Core) (hT : C.HasTests) (hC : C.TestCart) (hF : C.FibLaw)
    (φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left) (h : IsSquare C.a φ₂) {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    (a : Sp (OO p) ⟶ (C.GG ⊗ C.GG).left) (a₀ : Sp (PadicAlgCl p) ⟶ (C.A ⊗ C.A).left)
    (ha : a₀ ≫ φ₂ = gPt p ≫ a) (b : Sp (OO p) ⟶ C.P.left)
    (hb : gPt p ≫ b = a₀ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = a ≫ (C.GG ⊗ C.GG).hom)
    (a' : Sp (OO q) ⟶ (C.GG ⊗ C.GG).left) (a₁ : Sp (PadicAlgCl q) ⟶ (C.A ⊗ C.A).left)
    (ha' : a₁ ≫ φ₂ = gPt q ≫ a') (b' : Sp (OO q) ⟶ C.P.left)
    (hb₁ : gPt q ≫ b' = a₁ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb₁' : b' ≫ C.P.hom = a' ≫ (C.GG ⊗ C.GG).hom)
    (e : a (cPt p) = a' (cPt q)) : b (cPt p) = b' (cPt q) := by sorry
