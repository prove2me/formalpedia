-- Prove2me | Theorems.Thm_GlobalTheory_GenExtendNormal_mem_range_of_notMem
-- name    : GlobalTheory.GenExtendNormal.mem_range_of_notMem
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T00:52:26.572692+00:00
-- url     : https://prove2.me/theorems/7b4dc22b-40bd-41d2-8c27-d29e0370cc22
-- title:
--   Gen Extend Normal: mem range of not Mem
-- statement:
--   The Gen Extend Normal construction uses the mem range of not Mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueRigidifiedGeneratorExtendNormal.lean#L83-L185
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DegenerationProofs/ExistsUniqueRigidifiedGeneratorExtendNormal.lean#L83-L185

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

theorem GlobalTheory.GenExtendNormal.mem_range_of_notMem {S U H HU X : Scheme.{0}} [IsIntegral S] [IsLocallyNoetherian S]
    [GlobalTheory.IsNormalScheme S] [Nonempty U] [IsIntegral H] {j : U ⟶ S} [IsOpenImmersion j] {p : H ⟶ S}
    {e : S ⟶ H} {jH : HU ⟶ H} {pU : HU ⟶ U} {eU : U ⟶ HU} [Smooth p] [GeometricallyIntegral p]
    (he : e ≫ p = 𝟙 _) (hP : IsPullback jH pU p j) (heU : eU ≫ jH = j ≫ e) {L : LB X}
    (hL : L.IsLB) {I : Type} [Fintype I] {φ : I → (H ⟶ X)} {ε : I → ℤ}
    {t : LB.Gen (LB.LinComb L (fun i ↦ jH ≫ φ i) ε)}
    {ρ : LB.Gen (LB.LinComb L (fun i ↦ e ≫ φ i) ε)} (ht : t.IsGen) (hρ : ρ.IsGen)
    (hc : LB.Gen.Corr L _ _ _ _ (LB.pullGen L _ _ t eU) (LB.pullGen L _ _ ρ j))
    (x : H) (hx : Order.coheight x = 1) (hxU : p x ∉ Set.range j) (a : I → L.ι)
    (hxa : x ∈ LB.wchart L φ a) (A : H.Opens) [Nonempty A] (τ : Γ(H, A)ˣ)
    (hτ : ∀ (Z : Scheme.{0}) (r : Z ⟶ HU) (z : Z), jH (r z) ∈ A →
      gm (r ≫ jH) z A τ = gm r z (LB.wchart L (fun i ↦ jH ≫ φ i) a) (t.s a)) :
    H.germToFunctionField A τ.val ∈ (algebraMap (H.presheaf.stalk x) H.functionField).range ∧
    H.germToFunctionField A (τ⁻¹).val ∈ (algebraMap (H.presheaf.stalk x) H.functionField).range := by sorry
