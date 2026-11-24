-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_exists_proj
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.exists_proj
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:26:05.81673+00:00
-- url     : https://prove2.me/theorems/9e2b295f-85c7-4f91-a06a-92d4366964bf
-- title:
--   Hodge Alt: exists proj
-- statement:
--   The Hodge Alt construction uses the exists proj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L94-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L94-L102

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

theorem GlobalTheory.CompanionTheory.HodgeAlt.exists_proj (p q : V →ₗ[R] V') (h : Function.Bijective fun x : V × V ↦ p x.1 + q x.2) :
    ∃ P Q : V' →ₗ[R] V, (∀ v, P (p v) = v) ∧ (∀ v, P (q v) = 0) ∧ (∀ v, Q (p v) = 0) ∧
      ∀ v, Q (q v) = v := by sorry
