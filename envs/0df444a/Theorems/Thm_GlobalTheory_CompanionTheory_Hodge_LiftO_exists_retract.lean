-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_exists_retract
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.exists_retract
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T03:07:00.891227+00:00
-- url     : https://prove2.me/theorems/17edb5dc-e2be-48f7-9b23-eb527ccc98ad
-- title:
--   Lift O: exists retract
-- statement:
--   The Lift O construction uses the exists retract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L18-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L18-L26

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

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.exists_retract (P Q : V →ₗ[R] W) (hb : Function.Bijective fun x : V × V ↦ P x.1 + Q x.2) :
    ∃ r s : W →ₗ[R] V, (∀ x, r (P x) = x) ∧ (∀ x, r (Q x) = 0) ∧ (∀ x, s (P x) = 0) ∧ ∀ x, s (Q x) = x := by sorry
