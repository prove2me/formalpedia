-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_exists_nbhd
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.exists_nbhd
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-25T07:23:02.077083+00:00
-- url     : https://prove2.me/theorems/e9d5279c-9b95-45d8-b762-136c251d7eb2
-- title:
--   Iso Thick: exists nbhd
-- statement:
--   The Iso Thick construction uses the exists nbhd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L312-L361
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L312-L361

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

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.exists_nbhd {R : Type} [CommRing R] [IsNoetherianRing R] (I : Ideal R)
    (X C : Over (Spec (CommRingCat.of R))) (p : C ⟶ X) [IsProper X.hom] [IsProper p.left]
    (h : ∀ e, IsIso ((Over.pullback (thick R I e)).map p).left) (x : X.left)
    (hx : I ≤ (X.hom x).asIdeal) : ∃ W : X.left.Opens, x ∈ W ∧ IsIso (p.left ∣_ W) := by sorry
