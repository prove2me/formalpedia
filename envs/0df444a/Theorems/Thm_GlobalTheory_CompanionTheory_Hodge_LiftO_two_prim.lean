-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_two_prim
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.two_prim
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:24:02.307699+00:00
-- url     : https://prove2.me/theorems/3acf908d-1aaf-466f-8c90-07a6cf9d21cb
-- title:
--   Lift O: two prim
-- statement:
--   The Lift O construction uses the two prim property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L279-L305
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L279-L305

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
variable {R : Type} [CommRing R] {C E : Type} [Category.{0} C] [Category.{0} E]
  {F : C ⥤ CommAlgCat.{0} R} {G : E ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.two_prim (m p q : CoefMap (RingHom.id R) F G)
    (hW : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c) (hC : Closed1 F = ⊤) (f : Z1 F) (β : A0 F)
    (hβ : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), β T' = p1 F φ (β T) + KaehlerDifferential.D R _ (f.1 T T' φ)) (T : E) :
    qOm m 2 T (dOne R _ (β _)) = qOm p 2 T (dOne R _ (β _)) + qOm q 2 T (dOne R _ (β _)) := by sorry
