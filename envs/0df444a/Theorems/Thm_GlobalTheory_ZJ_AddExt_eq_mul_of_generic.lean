-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_AddExt_eq_mul_of_generic
-- name    : GlobalTheory.ZJ.AddExt.eq_mul_of_generic
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T15:16:08.049801+00:00
-- url     : https://prove2.me/theorems/87818081-d61b-4ca0-ba9a-3c6d3de3d96c
-- title:
--   Add Ext: eq mul of generic
-- statement:
--   The Add Ext construction uses the eq mul of generic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddExtension.lean#L78-L132
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddExtension.lean#L78-L132

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

theorem GlobalTheory.ZJ.AddExt.eq_mul_of_generic (C : Core) {p : ℕ} [Fact p.Prime] {y : Sp (OO p) ⟶ C.Z} (τ : C.Test y)
    (c d : Over.mk (spMap τ.j) ⟶ τ.H) (a₀ : Sp (PadicAlgCl p) ⟶ (C.A ⊗ C.A).left)
    (hc : a₀ ≫ (fst C.A C.A).left ≫ C.a = gPt p ≫ c.left ≫ τ.f)
    (hd : a₀ ≫ (snd C.A C.A).left ≫ C.a = gPt p ≫ d.left ≫ τ.f)
    (b : Sp (OO p) ⟶ C.P.left) (hb : gPt p ≫ b = a₀ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = y) :
    b = (c * d).left ≫ τ.f ≫ C.G.ι := by sorry
