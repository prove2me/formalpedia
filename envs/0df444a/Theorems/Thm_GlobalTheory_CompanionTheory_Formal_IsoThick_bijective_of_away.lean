-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_bijective_of_away
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.bijective_of_away
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:19:06.437837+00:00
-- url     : https://prove2.me/theorems/199119df-6790-5ef1-90c5-a108967ae90f
-- title:
--   Iso Thick: bijective of away
-- statement:
--   The Iso Thick construction uses the bijective of away property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L18-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L18-L65

import Mathlib
import Definitions.Def_PositivityTheory_PublishedTheorems_TowerLemmas_FormalTowerLemmas_Imports
import Definitions.Def_P2M_Def_Development_AbelianVarietyTheory_PublishedTheorems_Divisors__FormalAlgebraisation_7c2ebf494af3a4ae
import Definitions.Def_PositivityTheory_PublishedTheorems_UnitKilling_UnitAnnihilation_UnitAnnihilators_ExistsUnitKillsOfIdempotent
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_IsoOfThickenings
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

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.bijective_of_away {A B A' B' : Type} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (φ : A →+* B) (ρA : A →+* A') (ρB : B →+* B') (ψ : A' →+* B')
    (hc : ∀ a, ψ (ρA a) = ρB (φ a)) (s : A)
    (hA : @IsLocalization.Away _ _ s A' _ ρA.toAlgebra)
    (hB : @IsLocalization.Away _ _ (φ s) B' _ ρB.toAlgebra)
    (hker : ∀ k, φ k = 0 → s * k = 0) (hcok : ∀ b, ∃ a, φ s * b = φ a) :
    Function.Bijective ψ := by sorry
