-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_fibre_subsingleton
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.fibre_subsingleton
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:24:29.970339+00:00
-- url     : https://prove2.me/theorems/6c5efd1a-b1e8-44d6-95ba-1e8a83ee59af
-- title:
--   Iso Thick: fibre subsingleton
-- statement:
--   The Iso Thick construction uses the fibre subsingleton property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L263-L289
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L263-L289

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

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.fibre_subsingleton {R : Type} [CommRing R] (I : Ideal R)
    (X C : Over (Spec (CommRingCat.of R))) (p : C ⟶ X)
    (hiso : IsIso ((Over.pullback (thick R I 0)).map p).left) (c₁ c₂ : C.left)
    (h12 : p.left c₁ = p.left c₂) (hI : I ≤ (X.hom (p.left c₁)).asIdeal) : c₁ = c₂ := by sorry
