-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_ring_case
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.ring_case
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:18.952469+00:00
-- url     : https://prove2.me/theorems/ae9473d5-b7d1-53f9-8318-1f35f935ca22
-- title:
--   Iso Thick: ring case
-- statement:
--   The Iso Thick construction uses the ring case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L155-L172
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L155-L172

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

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.ring_case {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    [IsNoetherianRing A] (φ : A →ₐ[R] B) (hφ : φ.toRingHom.Finite) (I : Ideal R)
    (hf : ∀ e : ℕ, Function.Bijective
      (Algebra.TensorProduct.map φ (AlgHom.id R (R ⧸ I ^ (e + 1))))) :
    ∃ s : A, s - 1 ∈ I.map (algebraMap R A) ∧ (∀ k, φ k = 0 → s * k = 0) ∧
      ∀ b, ∃ a, φ s * b = φ a := by sorry
