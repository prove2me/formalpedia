-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_terminal_product_exponent_le
-- name    : OAI.PolycyclicRecognition.CartanWordModel.terminal_product_exponent_le
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T18:02:53.415669+00:00
-- url     : https://prove2.me/theorems/b6ff85dc-c6f8-415b-82b2-e5d13a249d68
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.terminal_product_exponent_le: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.terminal_product_exponent_le` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanTerminalComparison.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanTerminalComparison.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra MeasureTheory Filter Set Metric`, `open scoped Manifold Topology ENNReal`):
--
--   ```lean
--   theorem terminal_product_exponent_le
--       (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
--       (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
--       (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
--       (hchartN : ∀ x, chartN x = F.ExpN x)
--       (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
--       (hchartD : ∀ x, chartD x = F.ExpD x)
--       (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (μ : Measure F.N.carrier) [μ.IsHaarMeasure]
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (γ : M.Bases) {h : ℕ} (hh : 0 < h)
--       (scale RH η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
--       (hscale : ∀ n, 0 < scale n) (hRH0 : ∀ n, 0 ≤ RH n)
--       (hRH : HasSubexponentialUpperBoundSeq scale RH) (hη : Tendsto η atTop (𝓝 0))
--       (s : ℕ → Finset (Fin h → G))
--       (p : ℕ → (Fin h → G) → (Fin h → F.N.carrier) × (Fin h → F.D.carrier))
--       (U : Set ((Fin h → F.N.carrier) × (Fin h → F.D.carrier))) (hU : IsCompact U)
--       (I : ℕ → Set (Fin h → F.N.carrier)) (C : ℕ → Set F.N.carrier)
--       (t : ℕ → Finset G) {ρ R b c : ℝ}
--       (hp : ∀ n x, x ∈ s n → ∀ i,
--         F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i)
--       (hsmall : ∀ z ∈ U, dist (1 : Fin h → G)
--         (fun i => F.inclusionN (z.1 i) * F.inclusionD (z.2 i)) < ρ)
--       (hd : ∀ n x, x ∈ s n → ∀ i,
--         ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n)
--       (hhgt : ∀ n x, x ∈ s n → ∀ i,
--         ‖eW (heightProjection T.character
--           (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
--             η n * scale n)
--       (hI : ∀ n u, u ∈ I n → ∃ x ∈ s n, ∃ z ∈ U,
--         prefixCoordinateEquiv h u = fun i => (p n x).1 i * F.action ((p n x).2 i) (z.1 i))
--       (hC : ∀ᶠ n in atTop, C n ⊆ (fun u : Fin h → F.N.carrier => (List.ofFn u).prod) '' I n)
--       (hlower : HasSubexponentialLowerBoundSeq scale
--         (fun n => (μ (C n)).toReal / Real.exp (scale n * b)))
--       (hcover : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ y ∈ t n,
--         dist (x ⟨h - 1, Nat.sub_lt hh (by decide)⟩) y ≤ R)
--       (hcount : HasSubexponentialUpperBoundSeq scale
--         (fun n => ((t n).card : ℝ) / Real.exp (scale n * c))) : b ≤ c
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.CartanWordModel.Bases` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq` and `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.HasSubexponentialLowerBoundSeq` (definitions bundle `OAIQ093D003` of this split); `OAI.PolycyclicRecognition.cartanLog` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.prefixCoordinateEquiv` (definitions bundle `OAIQ093D005` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel`, `OAI.PolycyclicRecognition.heightProjection` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.source_target_product_exponent_le` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanTerminalComparison.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.terminal_product_exponent_le)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D004
import Definitions.Def_OAIQ093D005
import Definitions.Def_OAIQ093D008

section

attribute [-instance] _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra MeasureTheory Filter Set Metric
open scoped Manifold Topology ENNReal

variable {EG G W : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [ProperSpace G] [IsIsometricSMul G G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G, LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  [IsTopologicalGroup F.N.carrier]
  [SecondCountableTopology F.N.carrier]

set_option maxHeartbeats 1000000 in
include hunimod in
theorem terminal_product_exponent_le
    (hExpG : IsGroupExponential ExpG) (hinjG : Function.Injective ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (π : G →* Multiplicative W) (hπ : Continuous (fun g => (π g).toAdd))
    (hπExp : ∀ x, (π (ExpG x)).toAdd = eW (heightProjection T.character x))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ x, chartN x = F.ExpN x)
    (chartD : GroupLieAlgebra (𝓘(ℝ, F.D.modelSpace)) F.D.carrier ≃ₜ F.D.carrier)
    (hchartD : ∀ x, chartD x = F.ExpD x)
    (hbijN : Function.Bijective F.ExpN) (hbijD : Function.Bijective F.ExpD)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (dynkinD : NilpotentDynkinExpansionInput F.D.modelSpace F.D.carrier)
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (μ : Measure F.N.carrier) [μ.IsHaarMeasure]
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (γ : M.Bases) {h : ℕ} (hh : 0 < h)
    (scale RH η : ℕ → ℝ) (hs : Tendsto scale atTop atTop)
    (hscale : ∀ n, 0 < scale n) (hRH0 : ∀ n, 0 ≤ RH n)
    (hRH : HasSubexponentialUpperBoundSeq scale RH) (hη : Tendsto η atTop (𝓝 0))
    (s : ℕ → Finset (Fin h → G))
    (p : ℕ → (Fin h → G) → (Fin h → F.N.carrier) × (Fin h → F.D.carrier))
    (U : Set ((Fin h → F.N.carrier) × (Fin h → F.D.carrier))) (hU : IsCompact U)
    (I : ℕ → Set (Fin h → F.N.carrier)) (C : ℕ → Set F.N.carrier)
    (t : ℕ → Finset G) {ρ R b c : ℝ}
    (hp : ∀ n x, x ∈ s n → ∀ i,
      F.inclusionN ((p n x).1 i) * F.inclusionD ((p n x).2 i) = x i)
    (hsmall : ∀ z ∈ U, dist (1 : Fin h → G)
      (fun i => F.inclusionN (z.1 i) * F.inclusionD (z.2 i)) < ρ)
    (hd : ∀ n x, x ∈ s n → ∀ i,
      ‖(finBasis ℝ H).equivFun (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i))‖ ≤ RH n)
    (hhgt : ∀ n x, x ∈ s n → ∀ i,
      ‖eW (heightProjection T.character
        (cartanLog H F.D.equiv F.ExpD hbijD ((p n x).2 i) : GroupLieAlgebra (𝓘(ℝ, EG)) G))‖ ≤
          η n * scale n)
    (hI : ∀ n u, u ∈ I n → ∃ x ∈ s n, ∃ z ∈ U,
      prefixCoordinateEquiv h u = fun i => (p n x).1 i * F.action ((p n x).2 i) (z.1 i))
    (hC : ∀ᶠ n in atTop, C n ⊆ (fun u : Fin h → F.N.carrier => (List.ofFn u).prod) '' I n)
    (hlower : HasSubexponentialLowerBoundSeq scale
      (fun n => (μ (C n)).toReal / Real.exp (scale n * b)))
    (hcover : ∀ᶠ n in atTop, ∀ x ∈ s n, ∃ y ∈ t n,
      dist (x ⟨h - 1, Nat.sub_lt hh (by decide)⟩) y ≤ R)
    (hcount : HasSubexponentialUpperBoundSeq scale
      (fun n => ((t n).card : ℝ) / Real.exp (scale n * c))) : b ≤ c := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
