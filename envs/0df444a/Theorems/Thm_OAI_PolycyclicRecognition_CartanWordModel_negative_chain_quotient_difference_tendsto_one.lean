-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_negative_chain_quotient_difference_tendsto_one
-- name    : OAI.PolycyclicRecognition.CartanWordModel.negative_chain_quotient_difference_tendsto_one
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T19:09:07.678049+00:00
-- url     : https://prove2.me/theorems/f329f8b7-b92a-487e-8395-604bd5e99e4d
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.negative_chain_quotient_difference_tendsto_one: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.negative_chain_quotient_difference_tendsto_one` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNegativeChainAsymptotics.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNegativeChainAsymptotics.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Filter Set`, `open scoped Manifold Topology`):
--
--   ```lean
--   theorem negative_chain_quotient_difference_tendsto_one
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (γ₀ : M.Bases)
--       (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
--         (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
--         (cartanLog H F.D.equiv F.ExpD
--           (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
--       (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
--         ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
--           dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
--       {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
--       (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
--       (αW : W →L[ℝ] ℝ)
--       (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal
--         (positiveWeightRay (αW.toLinearMap.comp
--           (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))))
--       (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
--       (hExpQ : IsGroupExponential ExpQ)
--       (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
--       (hchartQ : ∀ v, chartQ v = ExpQ v)
--       (dynkinQ : NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
--       (π : F.N.carrier →* Q.carrier) (hπcont : Continuous π)
--       (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
--         ExpQ (Q.equiv (M.coneProjection (positiveWeightRay (αW.toLinearMap.comp
--           (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) x)))
--       (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
--       (hα : ∀ d n, α d (π n) = π (F.action d n))
--       (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
--       (sourceHeight : S → ℝ) (f : S → G) {L error : ℝ} (hL : 0 ≤ L)
--       (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
--       (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
--         |αW ((height (f x)).toAdd) - sourceHeight x| ≤ ε * dist 1 x + B)
--       (m : ℕ → ℕ) (z : ℕ → ℕ → S)
--       {R gap count : ℝ} (hR : 0 ≤ R) (hgap : 0 < gap) (countDegree : ℕ)
--       (hcount : ∀ᶠ n in atTop, (m n : ℝ) ≤ count * (1 + (n : ℝ)) ^ countDegree)
--       (hball : ∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n)
--       (hnegative : ∀ᶠ n in atTop, ∀ i ≤ m n, sourceHeight (z n i) ≤ -gap * n)
--       (hstep : ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1) :
--       Tendsto (fun n => (act (f (z n 0)) 1)⁻¹ * act (f (z n (m n))) 1)
--         atTop (𝓝 (1 : Q.carrier))
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.cartanRootIdeal` and `OAI.PolycyclicRecognition.CartanWordModel.Bases` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.positiveWeightRay` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.cartanLog` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.coneProjection` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.adjointGroupAutomorphism` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proofs of `OAI.PolycyclicRecognition.CartanWordModel.exists_boundary_family_with_compact_shadow` and `OAI.PolycyclicRecognition.CartanWordModel.ideal_fiber_quotient_difference_tendsto_one` of this split import it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanNegativeChainAsymptotics.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.negative_chain_quotient_difference_tendsto_one)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Filter Set
open scoped Manifold Topology

variable {EG G W S : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [IsIsometricSMul G G] [ProperSpace G]
  [MetricSpace S] [One S]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W) (height : G →* Multiplicative W)
  (hheight : ∀ x, (height (ExpG x)).toAdd = eW (heightProjection T.character x))
  (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
  (hchartN : ∀ x, chartN x = F.ExpN x)
  (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
  (hchartD : ∀ x, chartD x = F.ExpD x)
  (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
  (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)

set_option maxHeartbeats 1000000 in
include hunimod hheight dynkinD in
theorem negative_chain_quotient_difference_tendsto_one
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ₀ : M.Bases)
    (hφ : ∀ d, F.action d = M.adjointGroupAutomorphism T F.N.equiv F.ExpN F.isExpN
      (by rw [← show chartN = F.ExpN from funext hchartN]; exact chartN.bijective) dynkinN
      (cartanLog H F.D.equiv F.ExpD
        (by rw [← show chartD = F.ExpD from funext hchartD]; exact chartD.bijective) d))
    (hpath : ∀ g : G, ∃ γ : ℝ → G, γ 0 = 1 ∧ γ 1 = g ∧
      ∀ t ∈ Icc (0 : ℝ) 1, ∀ u ∈ Icc (0 : ℝ) 1,
        dist (γ t) (γ u) ≤ dist 1 g * |t - u|)
    {Kheight : ℝ} (hKheight : 0 ≤ Kheight)
    (hLip : ∀ x y, ‖(height x).toAdd - (height y).toAdd‖ ≤ Kheight * dist x y)
    (αW : W →L[ℝ] ℝ)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal
      (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype))))))
    (ExpQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier → Q.carrier)
    (hExpQ : IsGroupExponential ExpQ)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (hchartQ : ∀ v, chartQ v = ExpQ v)
    (dynkinQ : NilpotentDynkinExpansionInput Q.modelSpace Q.carrier)
    (π : F.N.carrier →* Q.carrier) (hπcont : Continuous π)
    (hπ : ∀ x : cartanRootIdeal H, π (F.ExpN (F.N.equiv x)) =
      ExpQ (Q.equiv (M.coneProjection (positiveWeightRay (αW.toLinearMap.comp
        (eW.toLinearMap.comp ((heightProjection T.character).comp H.subtype)))) x)))
    (α : F.D.carrier →* MulAut Q.carrier) (act : G →* Equiv.Perm Q.carrier)
    (hα : ∀ d n, α d (π n) = π (F.action d n))
    (hact : ∀ u d q, act (F.inclusionN u * F.inclusionD d) q = π u * α d q)
    (sourceHeight : S → ℝ) (f : S → G) {L error : ℝ} (hL : 0 ≤ L)
    (hf : ∀ x y, dist (f x) (f y) ≤ L * dist x y + error)
    (hsub : ∀ ε : ℝ, 0 < ε → ∃ B : ℝ, 0 ≤ B ∧ ∀ x,
      |αW ((height (f x)).toAdd) - sourceHeight x| ≤ ε * dist 1 x + B)
    (m : ℕ → ℕ) (z : ℕ → ℕ → S)
    {R gap count : ℝ} (hR : 0 ≤ R) (hgap : 0 < gap) (countDegree : ℕ)
    (hcount : ∀ᶠ n in atTop, (m n : ℝ) ≤ count * (1 + (n : ℝ)) ^ countDegree)
    (hball : ∀ᶠ n in atTop, ∀ i ≤ m n, dist 1 (z n i) ≤ R * n)
    (hnegative : ∀ᶠ n in atTop, ∀ i ≤ m n, sourceHeight (z n i) ≤ -gap * n)
    (hstep : ∀ᶠ n in atTop, ∀ i < m n, dist (z n i) (z n (i + 1)) ≤ 1) :
    Tendsto (fun n => (act (f (z n 0)) 1)⁻¹ * act (f (z n (m n))) 1)
      atTop (𝓝 (1 : Q.carrier)) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
