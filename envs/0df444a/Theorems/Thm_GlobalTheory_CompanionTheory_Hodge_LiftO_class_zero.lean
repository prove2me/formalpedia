-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_Hodge_LiftO_class_zero
-- name    : GlobalTheory.CompanionTheory.Hodge.LiftO.class_zero
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T03:09:36.325831+00:00
-- url     : https://prove2.me/theorems/fd9353dc-3c2c-5bce-bdb5-514dd355b7c4
-- title:
--   Lift O: class zero
-- statement:
--   The Lift O construction uses the class zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L204-L232
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExteriorPairingIotaTwo.lean#L204-L232

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

theorem GlobalTheory.CompanionTheory.Hodge.LiftO.class_zero (m p q : CoefMap (RingHom.id R) F G)
    (hH : Function.Bijective fun x : H1 F × H1 F ↦ p.pull1 x.1 + q.pull1 x.2)
    (hW : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c)
    (hmW : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω)
    (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F) (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG3 : ∀ (t : Z1 G ⊗[R] Glob1 G) (β : A0 G), (∀ T T' φ, muG t T T' φ = β T' - p1 G φ (β T)) →
      (H1.mk G).rTensor (Glob1 G) t = 0)
    (f : Z1 F) (t : Z1 F ⊗[R] Glob1 F)
    (ht : ∀ T T' φ, muF t T T' φ = KaehlerDifferential.D R _ (f.1 T T' φ)) :
    (H1.mk F).rTensor (Glob1 F) t = 0 := by sorry
