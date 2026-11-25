-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_LieModel_mem_htDual
-- name    : GlobalTheory.CompanionTheory.Ar.LieModel.mem_htDual
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:00:51.809827+00:00
-- url     : https://prove2.me/theorems/9c3c2c52-4f67-4084-a78f-e92d3875e631
-- title:
--   Lie Model: mem ht Dual
-- statement:
--   The Lie Model construction uses the mem ht Dual property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/MemEigSpOfMemHtDual.lean#L78-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/MemEigSpOfMemHtDual.lean#L78-L87

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_TwoWeightEqOneAddRoot
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_EigLat
import Definitions.Def_Development_AutomorphicSpectrum_Definitions_GlobalGeometry_MemEigSpOfMemHtDual
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Ar
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
variable {X : Scheme.{0}} {Ω : Type} [Field Ω]
variable {G : Over X} [GrpObj G] {ξ : Spec (CommRingCat.of Ω) ⟶ X} {E : Type} [AddCommGroup E] [Module Ω E]
open GlobalTheory.CompanionTheory.Ar.LieModel
variable (M : LieModel G ξ E) (L : LB G.left) (n : ℕ) {O : Type} [CommRing O] (ρ : O →+* Module.End Ω E)
  (σ : O →+* Ω)

theorem GlobalTheory.CompanionTheory.Ar.LieModel.mem_htDual (q : Cpt ξ) (e : eigSp ρ σ) :
    (e : E) ∈ M.htDual L n ρ σ q ↔ ∀ u ∈ M.htOmEig L n ρ σ q, u e ∈ regAt ξ q := by sorry
