-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Ar_Lat_patch_of_not
-- name    : GlobalTheory.CompanionTheory.Ar.Lat.patch_of_not
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T11:59:55.630695+00:00
-- url     : https://prove2.me/theorems/33ce9ee5-73af-4d4e-9252-f712830851e1
-- title:
--   Lat: patch of not
-- statement:
--   The Lat construction uses the patch of not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/MemEigSpOfMemHtDual.lean#L112-L114
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Definitions/GlobalGeometry/MemEigSpOfMemHtDual.lean#L112-L114

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

theorem GlobalTheory.CompanionTheory.Ar.Lat.patch_of_not (S : Finset ℕ) (L₀ : Lat ξ E) (Lp : ℕ → Lat ξ E) {q : Cpt ξ}
    (hq : ∀ p ∈ S, ¬ InFibre ξ p q) : Lat.patch S L₀ Lp q = L₀ q := by sorry
