-- Prove2me | Theorems.Thm_GlobalTheory_ZJ_AddExt_exists_test
-- name    : GlobalTheory.ZJ.AddExt.exists_test
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T15:16:36.643448+00:00
-- url     : https://prove2.me/theorems/2aa395f4-c09d-4f53-8880-e424ea9b0a5b
-- title:
--   Add Ext: exists test
-- statement:
--   The Add Ext construction uses the exists test property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddExtension.lean#L196-L221
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsAddExtension.lean#L196-L221

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

theorem GlobalTheory.ZJ.AddExt.exists_test (C : Core) (hT : C.HasTests) (hC : C.TestCart)
    (φ₂ : (C.A ⊗ C.A).left ⟶ (C.GG ⊗ C.GG).left) (h : IsSquare C.a φ₂) {p : ℕ} [Fact p.Prime]
    (a : Sp (OO p) ⟶ (C.GG ⊗ C.GG).left) (a₀ : Sp (PadicAlgCl p) ⟶ (C.A ⊗ C.A).left)
    (ha : a₀ ≫ φ₂ = gPt p ≫ a) (b : Sp (OO p) ⟶ C.P.left)
    (hb : gPt p ≫ b = a₀ ≫ (μ[C.A]).left ≫ C.a ≫ C.G.ι) (hb' : b ≫ C.P.hom = a ≫ (C.GG ⊗ C.GG).hom) :
    ∃ (τ : C.Test (a ≫ (C.GG ⊗ C.GG).hom)) (c d : Over.mk (spMap τ.j) ⟶ τ.H),
      c.left ≫ τ.f = a ≫ (fst C.GG C.GG).left ∧ d.left ≫ τ.f = a ≫ (snd C.GG C.GG).left ∧
      b = (c * d).left ≫ τ.f ≫ C.G.ι := by sorry
