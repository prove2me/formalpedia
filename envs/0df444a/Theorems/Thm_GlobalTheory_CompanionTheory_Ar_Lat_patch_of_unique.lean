-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_patch_of_unique
-- name    : GlobalTheory.CompanionTheory.Ar.Lat.patch_of_unique
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:00.251923+00:00
-- url     : https://prove2.me/theorems/04c5ab30-c4d7-554c-899c-d51195901690
-- title:
--   Lat: patch of unique
-- statement:
--   The Lat construction uses the patch of unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/MemEigSpOfMemHtDual.lean#L116-L120
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/MemEigSpOfMemHtDual.lean#L116-L120

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

theorem GlobalTheory.CompanionTheory.Ar.Lat.patch_of_unique (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ} {p : ℕ} (hp : p ∈ S)
    (hq : InFibre ξ p q) (hu : ∀ p' ∈ S, InFibre ξ p' q → p' = p) : Lat.patch S L₀ Lp q = Lp p q := by sorry
