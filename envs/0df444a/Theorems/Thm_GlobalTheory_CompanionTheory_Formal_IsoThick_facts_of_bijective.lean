-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_facts_of_bijective
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.facts_of_bijective
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:03.772868+00:00
-- url     : https://prove2.me/theorems/6eb1b6a4-8ac3-5476-9d76-b687be35e4f7
-- title:
--   Iso Thick: facts of bijective
-- statement:
--   The Iso Thick construction uses the facts of bijective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L82-L105
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L82-L105

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
open TensorProduct

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.facts_of_bijective {R A B : Type} [CommRing R] [CommRing A] [CommRing B] [Algebra R A]
    [Algebra R B] (φ : A →ₐ[R] B) (K : Ideal R)
    (h : Function.Bijective (Algebra.TensorProduct.map φ (AlgHom.id R (R ⧸ K)))) :
    (∀ a, φ a = 0 → a ∈ K.map (algebraMap R A)) ∧
      ∀ b, ∃ a, b - φ a ∈ K.map (algebraMap R B) := by sorry
