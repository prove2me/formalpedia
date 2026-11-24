-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exterior_pairing_iota_two
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.exterior_pairing_iota_two
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:21:51.787881+00:00
-- url     : https://prove2.me/theorems/d9d8a7d5-2254-4fdd-868b-78abd9623a2a
-- title:
--   Lift O: exterior pairing iota two
-- statement:
--   The Lift O construction uses the exterior pairing iota two property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L92-L93
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L92-L93

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExteriorPairingIotaTwo
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.Hodge GlobalTheory.CompanionTheory.Hodge.LiftO
variable {R V W V' W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [AddCommGroup V'] [Module R V'] [AddCommGroup W'] [Module R W']

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.exterior_pairing_iota_two (l u : V →ₗ[R] R) (a b : V) : pair2 l u (i2 a b) = l a * u b - u a * l b := by sorry
