-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HodgeAlt_two_zero
-- name    : GlobalTheory.CompanionTheory.HodgeAlt.two_zero
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:26:08.58588+00:00
-- url     : https://prove2.me/theorems/0eaf1b19-e481-4da1-922a-4ab418debb0d
-- title:
--   Hodge Alt: two zero
-- statement:
--   The Hodge Alt construction uses the two zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L419-L455
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ExistsOfRTensor.lean#L419-L455

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

theorem GlobalTheory.CompanionTheory.HodgeAlt.two_zero (m p q : CoefMap (RingHom.id R) F G) [Module.Finite R (Glob1 F)]
    [Module.Projective R (Glob1 F)] (nuF : ⋀[R]^2 (Glob1 F) →ₗ[R] W0 F 2)
    (nuG : ⋀[R]^2 (Glob1 G) →ₗ[R] W0 G 2)
    (hF : ∀ a b T, nuF (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hG : ∀ a b T, nuG (exteriorPower.ιMulti R 2 ![a, b]) T = wedge R _ (a.1 T) (b.1 T))
    (hinj : Function.Injective nuG)
    (hsur : ∀ w : W0 F 2, (∀ (T T' : C) (φ : T ⟶ T'), w T' = pOm F 2 φ (w T)) → ∃ t, nuF t = w)
    (hcG : Closed1 G = ⊤) (hsG : Function.Surjective (toO G))
    (hb2 : Function.Bijective fun x : Glob1 F × Glob1 F ↦ pullGlob1 p x.1 + pullGlob1 q x.2)
    (hm2 : ∀ ω, pullGlob1 m ω = pullGlob1 p ω + pullGlob1 q ω) (z : cechDeRhamTotalCocyclesTwo F) (h1 : z.1.1 = 0)
    (h2 : z.1.2.1 = 0)
    (h : pullHyp2 m (Hyp2.mk F z) = pullHyp2 p (Hyp2.mk F z) + pullHyp2 q (Hyp2.mk F z)) :
    z.1.2.2 = 0 := by sorry
