-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_uniform_contact_step_bridge_m
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_contact_step_bridge_m
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T23:17:05.16187+00:00
-- url     : https://prove2.me/theorems/e5d88613-2c65-405d-97df-202934148d49
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_contact_step_bridge_m: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_contact_step_bridge` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanContactStepBridge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanContactStepBridge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set Metric`, `open Filter`, `open scoped Manifold Pointwise Topology`):
--
--   ```lean
--   theorem exists_uniform_contact_step_bridge_m
--       [SimplyConnectedSpace G] [IsIsometricSMul G G]
--       (hExpG : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (hbijN : Function.Bijective F.ExpN)
--       (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
--       (hchartN : ∀ v, chartN v = F.ExpN v)
--       (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (letter : Fin M.letterCount) (h₀ : H) (hq : 0 < M.weight letter h₀)
--       {c B₀ : ℝ} (hc : 0 ≤ c) (hB₀ : 0 ≤ B₀) :
--       ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀
--       (ExpI : M.coneWordIdeal C → I)
--       (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
--       (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
--       (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
--       (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
--       (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
--       (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
--       (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
--       (πQ : F.N.carrier →* Q.carrier)
--       (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier)),
--       let Y := fun n => TiledProbeChainData.sourceCell (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
--         (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
--         (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
--         (D := D) (Q := Q) (chartQ := chartQ)
--         (πQ := πQ) (hι := hι) (hrange := hrange) n
--       let σ := TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
--         (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
--         (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
--         (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)
--       ∀ (R : ℕ → ℝ), Tendsto scale atTop atTop →
--         (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ R n) →
--         HasSubexponentialUpperBoundSeq scale R →
--       ∀ ε : ℝ, 0 < ε →
--       ∀ δ : ℝ, 0 ≤ δ → c * δ ≤ 1 →
--       ∀ (u step : ℕ → F.N.carrier) (time : ℕ → ℝ),
--         (∀ n, |time n| ≤ R n * Real.exp ((M.weight letter h₀ + B₀ * δ) * scale n)) →
--         (∀ n, F.inclusionN (step n) = Exp (time n •
--           (M.letter letter : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
--         ∀ᶠ n in atTop, ∀ y : Y n,
--           let S := M.sourceDilation T F hbijN chartN hchartN dynkinN
--             ((scale n * (1 - c * δ)) • h₀)
--           let k := S.symm (step n)
--           dist (F.inclusionN
--               (coneProbeSecond S.toMulEquiv (u n) (y.val.2 : F.N.carrier) k) *
--                 Exp (((scale n * (1 - c * δ)) • h₀ : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
--             (F.inclusionN (u n * S ((y.val.2 : F.N.carrier) * σ y.val.1)) *
--                 Exp (((scale n * (1 - c * δ)) • h₀ : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ≤
--             (A * δ + B * ε) * scale n
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.cartanRootIdeal` and `OAI.PolycyclicRecognition.CartanWordModel.Bases` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.coneProbeSecond` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData` and `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceSection` (definitions bundle `OAIQ093D020` of this split); `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceCell` (definitions bundle `OAIQ093D022` of this split); `OAI.PolycyclicRecognition.CartanWordModel.sourceDilation` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.exists_one_cone_offset_threshold` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanContactStepBridge.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_contact_step_bridge)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D022

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition.CartanWordModel

open Module LieAlgebra LieModule Set Metric
open Filter
open scoped Manifold Pointwise Topology

variable {EG G W I : Type} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G]
  [NormedAddCommGroup W] [NormedSpace ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (C : Set (H →ₗ[ℝ] ℝ))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
theorem exists_uniform_contact_step_bridge_m
    [SimplyConnectedSpace G] [IsIsometricSMul G G]
    (hExpG : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (hbijN : Function.Bijective F.ExpN)
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (letter : Fin M.letterCount) (h₀ : H) (hq : 0 < M.weight letter h₀)
    {c B₀ : ℝ} (hc : 0 ≤ c) (hB₀ : 0 ≤ B₀) :
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ ∀
    (ExpI : M.coneWordIdeal C → I)
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier)),
    let Y := fun n => TiledProbeChainData.sourceCell (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
      (D := D) (Q := Q) (chartQ := chartQ)
      (πQ := πQ) (hι := hι) (hrange := hrange) n
    let σ := TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
      (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
      (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor)
      (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)
    ∀ (R : ℕ → ℝ), Tendsto scale atTop atTop →
      (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ R n) →
      HasSubexponentialUpperBoundSeq scale R →
    ∀ ε : ℝ, 0 < ε →
    ∀ δ : ℝ, 0 ≤ δ → c * δ ≤ 1 →
    ∀ (u step : ℕ → F.N.carrier) (time : ℕ → ℝ),
      (∀ n, |time n| ≤ R n * Real.exp ((M.weight letter h₀ + B₀ * δ) * scale n)) →
      (∀ n, F.inclusionN (step n) = Exp (time n •
        (M.letter letter : GroupLieAlgebra (𝓘(ℝ, EG)) G))) →
      ∀ᶠ n in atTop, ∀ y : Y n,
        let S := M.sourceDilation T F hbijN chartN hchartN dynkinN
          ((scale n * (1 - c * δ)) • h₀)
        let k := S.symm (step n)
        dist (F.inclusionN
            (coneProbeSecond S.toMulEquiv (u n) (y.val.2 : F.N.carrier) k) *
              Exp (((scale n * (1 - c * δ)) • h₀ : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G))
          (F.inclusionN (u n * S ((y.val.2 : F.N.carrier) * σ y.val.1)) *
              Exp (((scale n * (1 - c * δ)) • h₀ : H) : GroupLieAlgebra (𝓘(ℝ, EG)) G)) ≤
          (A * δ + B * ε) * scale n := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
