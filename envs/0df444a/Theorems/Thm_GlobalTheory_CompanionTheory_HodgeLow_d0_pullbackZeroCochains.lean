-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeLow_d0_pullbackZeroCochains
-- name    : GlobalTheory.CompanionTheory.HodgeLow.d0_pullbackZeroCochains
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T22:24:40.975803+00:00
-- url     : https://prove2.me/theorems/39ee01f1-292a-42d9-96c7-9af20332331f
-- title:
--   Hodge Low: d0 pullback Zero Cochains
-- statement:
--   The Hodge Low construction uses the d0 pullback Zero Cochains property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L143-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/PullbackZeroCochainsAlgebraMap.lean#L143-L147

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_PullbackZeroCochainsAlgebraMap
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR MainStatements.Hodge
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeLow
variable {R : Type} [CommRing R] {C C' : Type} [Category.{0} C] [Category.{0} C']
  {F : C ⥤ CommAlgCat.{0} R} {F' : C' ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HodgeLow.d0_pullbackZeroCochains (m : CoefMap (RingHom.id R) F F') (g : C0 F) :
    d0 F' (pullbackZeroCochains m g) = pullbackOneCochains m (d0 F g) := by sorry
