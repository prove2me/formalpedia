-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_affine_case
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.affine_case
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T07:23:36.885786+00:00
-- url     : https://prove2.me/theorems/9f24b49d-4f4a-4415-bc39-ef32a5233d5d
-- title:
--   Iso Thick: affine case
-- statement:
--   The Iso Thick construction uses the affine case property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L194-L261
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L194-L261

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

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.affine_case {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (U V : Over (Spec (CommRingCat.of R))) (g : V ⟶ U) [IsAffine U.left] [IsAffine V.left]
    [IsProper g.left] [LocallyOfFiniteType U.hom]
    (h : ∀ e, IsIso ((Over.pullback (thick R I e)).map g).left) (x : U.left)
    (hx : I ≤ (U.hom x).asIdeal) :
    ∃ s : Γ(U.left, ⊤), x ∈ U.left.basicOpen s ∧ IsIso (g.left ∣_ U.left.basicOpen s) := by sorry
