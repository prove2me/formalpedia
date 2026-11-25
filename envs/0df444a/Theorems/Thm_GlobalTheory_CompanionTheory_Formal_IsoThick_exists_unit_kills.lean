-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_exists_unit_kills
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:13.866809+00:00
-- url     : https://prove2.me/theorems/b24b0612-8626-5c21-81b9-dbe74316dfd3
-- title:
--   Iso Thick: exists unit kills
-- statement:
--   The Iso Thick construction uses the exists unit kills property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L12-L16
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L12-L16

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_TowerLemmas_FormalTowerLemmas_Imports
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsoOfThickenings
import Theorems.Thm_KrullIntersectionUnits_KrullIntersectionLemmas_GlobalTheory_CompanionTheory_Formal_IsoThick_exists_unit_kills

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Out PositivityTheory.FormalThickening
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Formal GlobalTheory.CompanionTheory.Formal.IsoThick

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.exists_unit_kills {A B : Type} [CommRing A] [CommRing B] [IsNoetherianRing A] (φ : A →+* B)
    (hφ : φ.Finite) (J : Ideal A) (hsurj : ∀ b, ∃ a, b - φ a ∈ J.map φ)
    (hinj : ∀ a, φ a = 0 → ∀ n : ℕ, a ∈ J ^ n) :
    ∃ s : A, s - 1 ∈ J ∧ (∀ k, φ k = 0 → s * k = 0) ∧ ∀ b, ∃ a, φ s * b = φ a := by sorry
