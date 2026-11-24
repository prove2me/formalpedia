-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_one_cob
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.one_cob
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:24:54.236777+00:00
-- url     : https://prove2.me/theorems/94411895-0f4d-4ed4-97bc-6e607bcde091
-- title:
--   Hodge Alt: one cob
-- statement:
--   The Hodge Alt construction uses the one cob property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L368-L403
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L368-L403

import Mathlib
import Definitions.Def_Development_WeilBound_CoreStatements_TemperedRepresentationTheory_HodgeWedgeFields_H1CommutesBaseChange
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ExistsOfRTensor
import Theorems.Thm_GlobalTheory_CechDR_IsPull1_toO

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
variable {R : Type} [CommRing R] {C D : Type} [Category.{0} C] [Category.{0} D]
  {F : C ⥤ CommAlgCat.{0} R} {G : D ⥤ CommAlgCat.{0} R}

theorem GlobalTheory.CompanionTheory.HodgeAlt.one_cob (m p q : CoefMap (RingHom.id R) F G) (muF : Z1 F ⊗[R] Glob1 F →ₗ[R] A1 F)
    (muG : Z1 G ⊗[R] Glob1 G →ₗ[R] A1 G)
    (hF : ∀ f ω T T' φ, muF (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hG : ∀ f ω T T' φ, muG (f ⊗ₜ ω) T T' φ = f.1 T T' φ • ω.1 T')
    (hsur : ∀ a : A1 F, (∀ (T T' T'' : C) (φ : T ⟶ T') (ψ : T' ⟶ T''),
      a T T'' (φ ≫ ψ) = p1 F ψ (a T T' φ) + a T' T'' ψ) → ∃ t, muF t = a)
    (hker : ∀ (t : Z1 G ⊗[R] Glob1 G) (β : A0 G),
      (∀ T T' φ, muG t T T' φ = β T' - p1 G φ (β T)) → (H1.mk G).rTensor (Glob1 G) t = 0)
    (hsG : Function.Surjective (toO G))
    (hb1 : Function.Bijective fun x : H1 F × H1 F ↦ p.pull1 x.1 + q.pull1 x.2)
    (hb2 : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm1 : ∀ c, m.pull1 c = p.pull1 c + q.pull1 c)
    (hm2 : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω) (z : cechDeRhamTotalCocyclesTwo F) (hz : z.1.1 = 0)
    (h : pullHyp2 m (Hyp2.mk F z) = pullHyp2 p (Hyp2.mk F z) + pullHyp2 q (Hyp2.mk F z)) :
    ∃ β : A0 F, ∀ (T T' : C) (φ : T ⟶ T'), z.1.2.1 T T' φ = β T' - p1 F φ (β T) := by sorry
