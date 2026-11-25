-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Formal_IsoThick_over_pullback_fst
-- name    : GlobalTheory.CompanionTheory.Formal.IsoThick.over_pullback_fst
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T06:10:55.848671+00:00
-- url     : https://prove2.me/theorems/4c46af27-4879-4cdc-aace-1d0f4bc1ed36
-- title:
--   Iso Thick: over pullback fst
-- statement:
--   The Iso Thick construction uses the over pullback fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L174-L177
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/IsoOfThickenings.lean#L174-L177

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

theorem GlobalTheory.CompanionTheory.Formal.IsoThick.over_pullback_fst {S T : Scheme.{0}} (t : T ⟶ S) {P Q : Over S} (g : P ⟶ Q) :
    ((Over.pullback t).map g).left ≫ pullback.fst Q.hom t = pullback.fst P.hom t ≫ g.left := by sorry
