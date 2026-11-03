-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_CartanWordModel_exists_polar_tiled_probe_chains_from_box
-- name    : OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-02T19:09:20.233632+00:00
-- url     : https://prove2.me/theorems/21804432-2dfc-4b59-8c47-d9f0bed0db85
-- title:
--   OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarFixedSection.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarFixedSection.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition.CartanWordModel`, with `open Module LieAlgebra LieModule Set Metric`, `open scoped Manifold Pointwise`):
--
--   ```lean
--   theorem exists_polar_tiled_probe_chains_from_box
--       (hExp : IsGroupExponential Exp)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
--       (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       {ε : ℝ} (hε : 0 < ε) (β : M.ConeIdealBases C)
--       (data : M.TiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN ExpI ι bN
--         (normalizedPolarTemplates K ε) (fun _ => β))
--       (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n) (R : ℝ) (hR : 0 ≤ R)
--       (φ : ℕ → I ≃ₜ* I) (k : ℕ → F.N.carrier)
--       (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
--       (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
--       (tile : ∀ n, Fin (tiles n) → Set I)
--       (hm : ∀ n j, MeasurableSet (tile n j))
--       (hd : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l)))
--       (hu : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
--         ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0)) β (scale n) 1)
--       (ha₀ : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
--         ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 1)) β (scale n) 1)
--       (ht : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
--         ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 2)) β (scale n) R)) :
--       ∃ ambient : M.Bases,
--         ∃ D : M.TiledProbeChainData T F hunimod eW C ExpI bN
--           (normalizedPolarTemplates K ε) (fun _ => β) ambient
--           (fun i => ε * M.polarProbeWidths T hunimod eW K i) scale φ ι tiles anchor, D.bQ = data.bQ ∧ D.lift = data.lift
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal`, `OAI.PolycyclicRecognition.CartanWordModel.Bases`, `OAI.PolycyclicRecognition.CartanWordModel.wordList`, `OAI.PolycyclicRecognition.NilpotentLieModel`, `OAI.PolycyclicRecognition.SupportDatum.weightSupport` and `OAI.PolycyclicRecognition.WordBasisSelections.instFintype` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.normalizedPolarTemplates` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.CartanWordModel.supportIn` (definitions bundle `OAIQ093D007` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput`, `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` and `OAI.PolycyclicRecognition.CartanWordModel.heightConePreimage` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.CartanWordModel.polarProbeWidths` (definitions bundle `OAIQ093D014` of this split); `OAI.PolycyclicRecognition.CartanWordModel.ConeIdealBases`, `OAI.PolycyclicRecognition.CartanWordModel.coneIdealBox` and `OAI.PolycyclicRecognition.CartanWordModel.coneWordIdeal` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeChainData` (definitions bundle `OAIQ093D020` of this split); `OAI.PolycyclicRecognition.CartanWordModel.TiledProbeBoxData` (definitions bundle `OAIQ093D027` of this split); `OAI.PolycyclicRecognition.HeightSpace`, `OAI.PolycyclicRecognition.IsGroupExponential`, `OAI.PolycyclicRecognition.TriangularAdjoint`, `OAI.PolycyclicRecognition.heightKernel` and `OAI.PolycyclicRecognition.TriangularAdjoint.character` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.exists_normalized_polar_samplers` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanPolarFixedSection.lean (declaration OAI.PolycyclicRecognition.CartanWordModel.exists_polar_tiled_probe_chains_from_box)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D027
import Definitions.Def_OAIQ093D020

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.finiteSubgroupIndex_nonempty _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.instFiniteDimensionalRealSubtypeSemiDirectSumLieDerivationIdMemLieSubalgebraCartanNilshadow _root_.OAI.PolycyclicRecognition.natDownTotalComplexSymmetry _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_additive _root_.OAI.PolycyclicRecognition.subgroupInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.switchParametersMeasurableSpace _root_.Subgroup.finiteIndex_comap_compat _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list _root_.subgroup_map_finite _root_.torsion_characteristic
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
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G]
  [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H) [Nonempty (Fin M.letterCount)]
  {Exp : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H Exp)
  (hunimod : ∀ x : GroupLieAlgebra (𝓘(ℝ, EG)) G,
    LinearMap.trace ℝ _ (ad ℝ _ x) = 0)
  (eW : HeightSpace T.character ≃ₗ[ℝ] W)
  (K : ProperCone ℝ (StrongDual ℝ W))
  [Group I] [TopologicalSpace I] [IsTopologicalGroup I]
  [MeasurableSpace I] [BorelSpace I] [SecondCountableTopology I]

local notation "C" => heightConePreimage T eW K

set_option maxHeartbeats 1000000 in
omit [IsTopologicalGroup I] [BorelSpace I] [SecondCountableTopology I] in
theorem exists_polar_tiled_probe_chains_from_box
    (hExp : IsGroupExponential Exp)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (ExpI : M.coneWordIdeal C → I) (ι : I →* F.N.carrier)
    (bN : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    {ε : ℝ} (hε : 0 < ε) (β : M.ConeIdealBases C)
    (data : M.TiledProbeBoxData C T hunimod eW F.N.equiv F.ExpN ExpI ι bN
      (normalizedPolarTemplates K ε) (fun _ => β))
    (scale : ℕ → ℝ) (hr : ∀ n, 0 ≤ scale n) (R : ℝ) (hR : 0 ≤ R)
    (φ : ℕ → I ≃ₜ* I) (k : ℕ → F.N.carrier)
    (hφ : ∀ n z, ι (φ n z) = k n * ι z * (k n)⁻¹)
    (tiles : ℕ → ℕ) (anchor : ∀ n, Fin (tiles n) → I)
    (tile : ∀ n, Fin (tiles n) → Set I)
    (hm : ∀ n j, MeasurableSet (tile n j))
    (hd : ∀ n, Pairwise (fun j l => Disjoint (tile n j) (tile n l)))
    (hu : ∀ n, (⋃ j, tile n j) = M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 0)) β (scale n) 1)
    (ha₀ : ∀ n j, (φ n).symm (anchor n j) ∈ M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 1)) β (scale n) 1)
    (ht : ∀ n j, tile n j ⊆ anchor n j • ((φ n) '' M.coneIdealBox C ExpI
      ((M.supportIn T hunimod eW).weightSupport (normalizedPolarTemplates K ε 2)) β (scale n) R)) :
    ∃ ambient : M.Bases,
      ∃ D : M.TiledProbeChainData T F hunimod eW C ExpI bN
        (normalizedPolarTemplates K ε) (fun _ => β) ambient
        (fun i => ε * M.polarProbeWidths T hunimod eW K i) scale φ ι tiles anchor, D.bQ = data.bQ ∧ D.lift = data.lift := by
  sorry

end PolycyclicRecognition.CartanWordModel

end

end OAI
end
