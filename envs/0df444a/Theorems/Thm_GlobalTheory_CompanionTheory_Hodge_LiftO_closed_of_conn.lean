-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_closed_of_conn
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.closed_of_conn
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T22:23:10.617123+00:00
-- url     : https://prove2.me/theorems/e8a745e8-2d40-496d-a633-d378298da133
-- title:
--   Lift O: closed of conn
-- statement:
--   The Lift O construction uses the closed of conn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L307-L334
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L307-L334

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

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.closed_of_conn (m p q : CoefMap (RingHom.id R) F G) [Module.Finite R (Glob1 F)]
    [Module.Projective R (Glob1 F)]
    (hW : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c)
    (hmW : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω)
    (hC : Closed1 F = ⊤)
    (νF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2) (νG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, νF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, νG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hinj : Function.Injective νG)
    (hsurj : ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, νF t = w)
    (f : Z1 F) (β : A0 F)
    (hβ : ∀ ⦃T T' : C⦄ (φ : T ⟶ T'), β T' = p1 F φ (β T) + KaehlerDifferential.D R _ (f.1 T T' φ)) (T : C) :
    dOne R _ (β T) = 0 := by sorry
