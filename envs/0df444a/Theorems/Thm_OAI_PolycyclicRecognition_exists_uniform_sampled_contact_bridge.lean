-- Prove2me | Theorems.Thm_OAI_PolycyclicRecognition_exists_uniform_sampled_contact_bridge
-- name    : OAI.PolycyclicRecognition.exists_uniform_sampled_contact_bridge
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-01T16:52:48.318206+00:00
-- url     : https://prove2.me/theorems/7ad10fdf-9375-46b8-88e3-b49dce7b7191
-- title:
--   OAI.PolycyclicRecognition.exists_uniform_sampled_contact_bridge: intermediate lemma from OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.PolycyclicRecognition.group_recognition`, `OAI.PolycyclicRecognition.lattice_recognition` and `OAI.PolycyclicRecognition.main_uniform_bounded_height`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Quasi-isometric recognition of virtually polycyclic groups (result family 255)*, OpenAI Math Release, September 24, 2026, result family 255, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.PolycyclicRecognition.exists_uniform_sampled_contact_bridge` of [lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanUniformContactBridge.lean](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanUniformContactBridge.lean) at commit 7ef5c0c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.PolycyclicRecognition`, with `open Module LieAlgebra Filter Set`, `open scoped Manifold Topology`):
--
--   ```lean
--   theorem exists_uniform_sampled_contact_bridge
--       (hExpG : IsGroupExponential ExpG)
--       (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
--       (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
--       (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
--       (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
--       (S : H → MulAut F.N.carrier)
--       (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
--         F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
--       (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
--       (letter : Fin M.letterCount) (h₀ : H) (hq : 0 < M.weight letter h₀)
--       {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) :
--       ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
--         ∀ {d : ℕ} (σ : (Fin d → ℝ) →ₗ[ℝ] cartanRootIdeal H)
--           {Z : Set (Fin d → ℝ)}, IsCompact Z →
--         ∀ (scale R : ℕ → ℝ), Tendsto scale atTop atTop →
--           (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ R n) →
--           HasSubexponentialUpperBoundSeq scale R →
--         ∀ ε : ℝ, 0 < ε →
--         ∀ᶠ j in atTop, ∀ δ : ℝ, 0 ≤ δ → c * δ ≤ 1 →
--           ∀ (u i sample : F.N.carrier) (x : G) (t : ℝ) (z : Fin d → ℝ),
--           |t| ≤ R j * Real.exp ((M.weight letter h₀ + B * δ) * scale j) → z ∈ Z →
--           let h := (scale j * (1 - c * δ)) • h₀
--           let k := (S h).symm (F.ExpN (F.N.equiv (t • M.letter letter)))
--           dist (x * F.inclusionN (sample * coneProbeSecond (S h) u i k) *
--               F.inclusionD (F.ExpD (F.D.equiv h)))
--             (x * F.inclusionN
--               (sample * coneProbeFirst (S h) u i (F.ExpN (F.N.equiv (σ z)))) *
--               F.inclusionD (F.ExpD (F.D.equiv h))) ≤
--             (C * δ + D * ε) * scale j
--   ```
--
--   **Definitions.** The statement is written with `TangentSpace.instFiniteDimensionalCompat`, `OAI.PolycyclicRecognition.CartanFactorModel`, `OAI.PolycyclicRecognition.CartanWordModel`, `OAI.PolycyclicRecognition.cartanRootIdeal` and `OAI.PolycyclicRecognition.NilpotentLieModel` (definitions bundle `OAIQ093D001` of this split); `OAI.PolycyclicRecognition.HasSubexponentialUpperBoundSeq`, `OAI.PolycyclicRecognition.NilpotentExponentialHaarInput` and `OAI.PolycyclicRecognition.coneProbeSecond` (definitions bundle `OAIQ093D002` of this split); `OAI.PolycyclicRecognition.coneProbeFirst` (definitions bundle `OAIQ093D004` of this split); `OAI.PolycyclicRecognition.ExponentialLinearRealizationInput` and `OAI.PolycyclicRecognition.NilpotentDynkinExpansionInput` (definitions bundle `OAIQ093D008` of this split); `OAI.PolycyclicRecognition.cartanIdealWeightDilation` (definitions bundle `OAIQ093D016` of this split); `OAI.PolycyclicRecognition.IsGroupExponential` and `OAI.PolycyclicRecognition.TriangularAdjoint` (the published bundle `Def_PolycyclicRecognition`).
--
--   **Used by.** The proof of `OAI.PolycyclicRecognition.CartanWordModel.exists_uniform_contact_step_bridge` of this split imports it.
-- source:
--   OpenAI, Quasi-isometric recognition of virtually polycyclic groups (result family 255), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 255; paper: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/preprints/quasi-isometric-recognition-of-virtually-polycyclic-groups-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/GroupTheory/PolycyclicRecognition/Geometry/CartanUniformContactBridge.lean (declaration OAI.PolycyclicRecognition.exists_uniform_sampled_contact_bridge)

import Mathlib
import Definitions.Def_PolycyclicRecognition
import Definitions.Def_OAIQ093D016

section

attribute [-instance] _root_.MeasureTheory.Measure.IsHaarMeasure.isInvInvariant_of_isMulRightInvariant _root_.OAI.PolycyclicRecognition.CartanWordModel.instDecidableEqConeMixedWords _root_.OAI.PolycyclicRecognition.CartanWordModel.instFintypeConeMixedWords _root_.OAI.PolycyclicRecognition.RationalQuotient.instIsLeftAdjointRepRatQuotientSubgroupQuotientToCoinvariantsFunctor_solutions _root_.OAI.PolycyclicRecognition.RationalQuotient.normalCoinvariants_preservesProjective _root_.OAI.PolycyclicRecognition.RationalQuotient.quotientCoinvariants_additive _root_.OAI.PolycyclicRecognition.groupCohomology_integral_additive _root_.OAI.PolycyclicRecognition.normalInduction_additive _root_.OAI.PolycyclicRecognition.normalInduction_preservesHomology _root_.OAI.PolycyclicRecognition.normalInduction_preservesMonomorphisms _root_.OAI.PolycyclicRecognition.normalInduction_preservesProjectives _root_.OAI.PolycyclicRecognition.productExpression_nonempty _root_.simple_finite_list
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace PolycyclicRecognition

open Module LieAlgebra Filter Set
open scoped Manifold Topology

variable {EG G : Type*} [NormedAddCommGroup EG] [NormedSpace ℝ EG]
  [FiniteDimensional ℝ EG] [MetricSpace G] [ChartedSpace EG G] [Group G]
  [LieGroup (𝓘(ℝ, EG)) ⊤ G] [SimplyConnectedSpace G] [IsIsometricSMul G G]
  {a : ℕ} (T : TriangularAdjoint (GroupLieAlgebra (𝓘(ℝ, EG)) G) a)
  {H : LieSubalgebra ℝ (GroupLieAlgebra (𝓘(ℝ, EG)) G)} [H.IsCartanSubalgebra]
  (M : CartanWordModel H)
  {ExpG : GroupLieAlgebra (𝓘(ℝ, EG)) G → G} (F : CartanFactorModel H ExpG)

set_option maxHeartbeats 1000000 in
theorem exists_uniform_sampled_contact_bridge
    (hExpG : IsGroupExponential ExpG)
    (realize : ExponentialLinearRealizationInput (EG := EG) (G := G))
    (haarN : NilpotentExponentialHaarInput F.N.modelSpace F.N.carrier)
    (haarD : NilpotentExponentialHaarInput F.D.modelSpace F.D.carrier)
    (dynkinN : NilpotentDynkinExpansionInput F.N.modelSpace F.N.carrier)
    (S : H → MulAut F.N.carrier)
    (hS : ∀ h v, S h (F.ExpN (F.N.equiv v)) =
      F.ExpN (F.N.equiv (cartanIdealWeightDilation T H h v)))
    (b₀ : Basis (Fin (finrank ℝ (cartanRootIdeal H))) ℝ (cartanRootIdeal H))
    (letter : Fin M.letterCount) (h₀ : H) (hq : 0 < M.weight letter h₀)
    {c B : ℝ} (hc : 0 ≤ c) (hB : 0 ≤ B) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧
      ∀ {d : ℕ} (σ : (Fin d → ℝ) →ₗ[ℝ] cartanRootIdeal H)
        {Z : Set (Fin d → ℝ)}, IsCompact Z →
      ∀ (scale R : ℕ → ℝ), Tendsto scale atTop atTop →
        (∀ n, 0 ≤ scale n) → (∀ n, 0 ≤ R n) →
        HasSubexponentialUpperBoundSeq scale R →
      ∀ ε : ℝ, 0 < ε →
      ∀ᶠ j in atTop, ∀ δ : ℝ, 0 ≤ δ → c * δ ≤ 1 →
        ∀ (u i sample : F.N.carrier) (x : G) (t : ℝ) (z : Fin d → ℝ),
        |t| ≤ R j * Real.exp ((M.weight letter h₀ + B * δ) * scale j) → z ∈ Z →
        let h := (scale j * (1 - c * δ)) • h₀
        let k := (S h).symm (F.ExpN (F.N.equiv (t • M.letter letter)))
        dist (x * F.inclusionN (sample * coneProbeSecond (S h) u i k) *
            F.inclusionD (F.ExpD (F.D.equiv h)))
          (x * F.inclusionN
            (sample * coneProbeFirst (S h) u i (F.ExpN (F.N.equiv (σ z)))) *
            F.inclusionD (F.ExpD (F.D.equiv h))) ≤
          (C * δ + D * ε) * scale j := by
  sorry

end PolycyclicRecognition

end

end OAI
end
