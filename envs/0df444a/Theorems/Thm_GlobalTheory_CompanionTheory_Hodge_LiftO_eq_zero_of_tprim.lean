-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_eq_zero_of_tprim
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.eq_zero_of_tprim
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:22:52.529874+00:00
-- url     : https://prove2.me/theorems/1e0105ed-9e8a-4ded-93f7-33cb17aee5a2
-- title:
--   Lift O: eq zero of tprim
-- statement:
--   The Lift O construction uses the eq zero of tprim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L28-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L28-L43

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

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.eq_zero_of_tprim (P₁ Q₁ : V →ₗ[R] W) (P₂ Q₂ : V' →ₗ[R] W')
    (h₁ : Function.Bijective fun x : V × V ↦ P₁ x.1 + Q₁ x.2)
    (h₂ : Function.Bijective fun x : V' × V' ↦ P₂ x.1 + Q₂ x.2) (z : V ⊗[R] V')
    (h : TensorProduct.map (P₁ + Q₁) (P₂ + Q₂) z = TensorProduct.map P₁ P₂ z + TensorProduct.map Q₁ Q₂ z) :
    z = 0 := by sorry
