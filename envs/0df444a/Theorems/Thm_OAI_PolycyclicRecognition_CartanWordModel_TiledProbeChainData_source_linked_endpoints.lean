-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_TiledProbeChainData_source_linked_endpoints
-- name    : OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_linked_endpoints
-- status  : Open
-- author  : @dbenbenn
-- created : 2026-11-02T19:26:45.790676+00:00
-- url     : https://prove2.me/theorems/34eb19b2-ec44-4d4a-8779-09bc125ef31a
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_linked_endpoints: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_linked_endpoints` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanTiledSourceEndpoints.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanTiledSourceEndpoints.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set Metric`, `open scoped Manifold Pointwise`):
--
--   ```lean
--   theorem TiledProbeChainData.source_linked_endpoints
--       (hchartN : ∀ v, chartN v = F.ExpN v)
--       (k u : ℕ → F.N.carrier) (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
--       (S : ℕ → MulAut F.N.carrier)
--       (E' : Fin 3 → Set W) (γ : M.Bases) (t' : Fin M.letterCount → ℝ)
--       (P : ∀ j, M.BoxProbeChains T F hunimod eW bN (E' j) γ t' scale
--         (fun n (y : Y n) => S n (D.probe n j (ψ n y))))
--       (origin base : ℕ → cartanRootIdeal H) (ε : ℕ → ℝ)
--       (L : M.LinkedProbeChains T F hunimod eW bN E' γ t' scale
--         (fun j n (y : Y n) => S n (D.probe n j (ψ n y))) P
--         (fun n _ => origin n) (fun n _ => base n) ε)
--       (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = u n)
--       (hbase : ∀ n, F.ExpN (F.N.equiv (base n)) = u n * S n (k n))
--       (n : ℕ) (y : Y n) :
--       F.ExpN (F.N.equiv (L.vertex 0 n y (Fin.last (P 0).length))) =
--         u n * S n ((y.val.2 : F.N.carrier) * σ y.val.1) ∧
--       F.ExpN (F.N.equiv (L.vertex 1 n y (Fin.last (P 1).length))) =
--         coneProbeSecond (S n) (u n) (ι (anchor n (D.index n (ψ n y).2))) (k n) ∧
--       F.ExpN (F.N.equiv (L.vertex 2 n y (Fin.last (P 2).length))) =
--         coneProbeSecond (S n) (u n) (y.val.2 : F.N.carrier) (k n)
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.coneProbeSecond` and `OAI.PolycyclicRecognition.kernelRealization` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.CartanWordModel.BoxProbeChains` and `OAI.PolycyclicRecognition.CartanWordModel.LinkedProbeChains` (definitions bundle `OAIQ093D013` of this split); `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealBox` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceCoordinates`, `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceQuotientCoordinates` and `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceSection` (definitions bundle `OAIQ093D020` of this split); `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.sourceCell` (definitions bundle `OAIQ093D022` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.PolarTiledSamplerData.nonempty_linkedSource_of_exp` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanTiledSourceEndpoints.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData.source_linked_endpoints)

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
open scoped Manifold Pointwise

variable {EG G W I : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
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

variable
    (ExpI : M.coneWordIdeal C → I)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (E : Fin 3 → Set W) (β : Fin 3 → M.ConeIdealBases C)
    (ambient : M.Bases) (t : Fin M.letterCount → ℝ) (scale : ℕ → ℝ)
    (φ : ℕ → I ≃ₜ* I) (ι : I →* F.N.carrier)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (D : M.TiledProbeChainData T F hunimod eW C ExpI bN E β ambient t scale φ ι tiles anchor)
    (Q : NilpotentLieModel ((cartanRootIdeal H) ⧸ M.coneWordIdeal C))
    (chartN : GroupLieAlgebra (𝓘(ℝ, F.N.modelSpace)) F.N.carrier ≃ₜ F.N.carrier)
    (chartQ : GroupLieAlgebra (𝓘(ℝ, Q.modelSpace)) Q.carrier ≃ₜ Q.carrier)
    (πQ : F.N.carrier →* Q.carrier)
    (hι : Topology.IsClosedEmbedding ι) (hrange : range ι = (πQ.ker : Set F.N.carrier))

local notation "Y" => fun n => TiledProbeChainData.sourceCell (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "ψ" => fun n => TiledProbeChainData.sourceCoordinates (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (πQ := πQ) (hι := hι) (hrange := hrange) n
local notation "σ" => TiledProbeChainData.sourceSection (T := T) (M := M) (F := F) (hunimod := hunimod) (eW := eW) (C := C)
    (ExpI := ExpI) (bN := bN) (E := E) (β := β) (ambient := ambient) (t := t)
    (scale := scale) (φ := φ) (ι := ι) (tiles := tiles) (anchor := anchor) (D := D) (Q := Q) (chartQ := chartQ) (chartN := chartN)

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
theorem TiledProbeChainData.source_linked_endpoints
    (hchartN : ∀ v, chartN v = F.ExpN v)
    (k u : ℕ → F.N.carrier) (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (S : ℕ → MulAut F.N.carrier)
    (E' : Fin 3 → Set W) (γ : M.Bases) (t' : Fin M.letterCount → ℝ)
    (P : ∀ j, M.BoxProbeChains T F hunimod eW bN (E' j) γ t' scale
      (fun n (y : Y n) => S n (D.probe n j (ψ n y))))
    (origin base : ℕ → cartanRootIdeal H) (ε : ℕ → ℝ)
    (L : M.LinkedProbeChains T F hunimod eW bN E' γ t' scale
      (fun j n (y : Y n) => S n (D.probe n j (ψ n y))) P
      (fun n _ => origin n) (fun n _ => base n) ε)
    (horigin : ∀ n, F.ExpN (F.N.equiv (origin n)) = u n)
    (hbase : ∀ n, F.ExpN (F.N.equiv (base n)) = u n * S n (k n))
    (n : ℕ) (y : Y n) :
    F.ExpN (F.N.equiv (L.vertex 0 n y (Fin.last (P 0).length))) =
      u n * S n ((y.val.2 : F.N.carrier) * σ y.val.1) ∧
    F.ExpN (F.N.equiv (L.vertex 1 n y (Fin.last (P 1).length))) =
      coneProbeSecond (S n) (u n) (ι (anchor n (D.index n (ψ n y).2))) (k n) ∧
    F.ExpN (F.N.equiv (L.vertex 2 n y (Fin.last (P 2).length))) =
      coneProbeSecond (S n) (u n) (y.val.2 : F.N.carrier) (k n) := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
