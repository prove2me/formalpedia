-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_eq_zero_of_prim
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.eq_zero_of_prim
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T22:22:48.006305+00:00
-- url     : https://prove2.me/theorems/795ab633-07cc-4820-8c0e-6a5e2ccb6367
-- title:
--   Lift O: eq zero of prim
-- statement:
--   The Lift O construction uses the eq zero of prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L150-L166
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L150-L166

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

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.eq_zero_of_prim [Module.Finite R V] [Module.Projective R V] (P Q : V →ₗ[R] W)
    (hb : Function.Bijective fun x : V × V ↦ P x.1 + Q x.2) (t : ⋀[R]^2 V)
    (h : exteriorPower.map 2 (P + Q) t = exteriorPower.map 2 P t + exteriorPower.map 2 Q t) : t = 0 := by sorry
