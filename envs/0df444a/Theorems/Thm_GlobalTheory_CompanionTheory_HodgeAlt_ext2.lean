-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_ext2
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.ext2
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:34:32.310479+00:00
-- url     : https://prove2.me/theorems/1b1417ab-4bd8-4850-ada3-7f3843214653
-- title:
--   Hodge Alt: ext2
-- statement:
--   The Hodge Alt construction uses the ext2 property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L135-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L135-L142

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
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
open KaehlerDifferential
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HodgeAlt
variable {R V V' W W' : Type} [CommRing R] [AddCommGroup V] [AddCommGroup V'] [AddCommGroup W]
  [AddCommGroup W'] [Module R V] [Module R V'] [Module R W] [Module R W']

theorem GlobalTheory.CompanionTheory.HodgeAlt.ext2 {N : Type} [AddCommGroup N] [Module R N] {f g : ⋀[R]^2 V →ₗ[R] N}
    (h : ∀ a b, f (exteriorPower.ιMulti R 2 ![a, b]) = g (exteriorPower.ιMulti R 2 ![a, b])) :
    f = g := by sorry
