-- Prove2me | Theorems.Thm_GlobalTheory_GenExtendNormal_exists_gen_germ
-- name    : GlobalTheory.GenExtendNormal.exists_gen_germ
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T00:53:05.6429+00:00
-- url     : https://prove2.me/theorems/3603a79c-dd1e-4e1b-989f-299b772e9931
-- title:
--   Gen Extend Normal: exists gen germ
-- statement:
--   The Gen Extend Normal construction uses the exists gen germ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueRigidifiedGeneratorExtendNormal.lean#L61-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueRigidifiedGeneratorExtendNormal.lean#L61-L81

import Mathlib
import Definitions.Def_ReciprocityTheory_ReductiveGroups_ArithmeticGeometry_BirationalGeometry_ToroidalCompactification_UniformisationConclusion
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AbelianSchemeLawProofs_ExistsUniqueGeneratorExtendDiscreteValuationRing
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ExistsUniqueLbIsoPullEqOfCoheightLeOne
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DegenerationProofs_ExistsUniqueRigidifiedGeneratorExtendNormal
import Theorems.Thm_P2M_GlobalTheory_normal_domain_height_one__5612c3bf64ed

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
set_option backward.isDefEq.respectTransparency false
open GlobalTheory GlobalTheory.GenExtendNormal
open GlobalTheory.DvrModel

theorem GlobalTheory.GenExtendNormal.exists_gen_germ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] {H X : Scheme.{0}}
    (p : H ⟶ Spec (CommRingCat.of V)) (e : Spec (CommRingCat.of V) ⟶ H) (hs : Smooth p)
    (hg : GeometricallyIntegral p) (he : e ≫ p = 𝟙 _)
    (eK : Spec (CommRingCat.of K) ⟶ pullback p (etaK V K))
    (heK : eK ≫ pullback.fst p (etaK V K) = etaK V K ≫ e) {L : LB X} (hL : L.IsLB)
    {I : Type} [Fintype I] (φ : I → (H ⟶ X)) (ε : I → ℤ)
    (ψ : I → (pullback p (etaK V K) ⟶ X)) (hψ : ψ = fun i ↦ pullback.fst p (etaK V K) ≫ φ i)
    (χ : I → (Spec (CommRingCat.of V) ⟶ X)) (hχ : χ = fun i ↦ e ≫ φ i)
    (t : LB.Gen (LB.LinComb L ψ ε)) (ρ : LB.Gen (LB.LinComb L χ ε)) (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eK) (LB.pullGen L _ _ ρ (etaK V K))) :
    ∃ c : LB.Gen (LB.LinComb L φ ε), ∀ z a, pullback.fst p (etaK V K) z ∈ LB.wchart L φ a →
      gm (pullback.fst p (etaK V K)) z (LB.wchart L φ a) (c.s a) =
        gm (𝟙 _) z (LB.wchart L ψ a) (t.s a) := by sorry
