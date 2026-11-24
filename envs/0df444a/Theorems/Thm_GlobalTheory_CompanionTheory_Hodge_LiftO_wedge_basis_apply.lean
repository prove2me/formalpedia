-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_wedge_basis_apply
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.wedge_basis_apply
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:56.1168+00:00
-- url     : https://prove2.me/theorems/7bdb101d-5391-437b-8960-2c1e24b1c10e
-- title:
--   Lift O: wedge basis apply
-- statement:
--   The Lift O construction uses the wedge basis apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L79-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L79-L79

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

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.wedge_basis_apply (a b : V) : b2 (R := R) a b = i2 a b := by sorry
