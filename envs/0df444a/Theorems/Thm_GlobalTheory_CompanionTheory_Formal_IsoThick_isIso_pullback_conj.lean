-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_isIso_pullback_conj
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.isIso_pullback_conj
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T07:20:01.611358+00:00
-- url     : https://prove2.me/theorems/38d0e1c8-75b9-5d2d-a9ad-aaac65d310c3
-- title:
--   Iso Thick: is Iso pullback conj
-- statement:
--   The Iso Thick construction uses the is Iso pullback conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L184-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L184-L192

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

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.isIso_pullback_conj {S T : Scheme.{0}} (t : T ⟶ S) {P Q P' Q' : Over S} (g : P ⟶ Q)
    (eP : P ≅ P') (eQ : Q ≅ Q') (h : IsIso ((Over.pullback t).map g).left) :
    IsIso ((Over.pullback t).map (eP.inv ≫ g ≫ eQ.hom)).left := by sorry
