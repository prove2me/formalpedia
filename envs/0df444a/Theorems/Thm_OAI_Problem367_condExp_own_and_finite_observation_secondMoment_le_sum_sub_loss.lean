-- Prove2me | Theorems.Thm_OAI_Problem367_condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss
-- name    : OAI.Problem367.condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-11T01:40:29.281652+00:00
-- url     : https://prove2.me/theorems/0bbc88ea-2706-4181-b924-ab0a37af0e9b
-- title:
--   OAI.Problem367.condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss: intermediate lemma from OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.Problem367.free_ising_factor_iff_threshold`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The sharp factor-of-IID threshold for the free Ising model on regular trees*, OpenAI Math Release, September 26, 2026, result family 236, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.Problem367.condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss` of [lean/OAI/Probability/FreeIsing/Conditioning/FiniteObservationInformation.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Conditioning/FiniteObservationInformation.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.Problem367`, with `open MeasureTheory ProbabilityTheory`, `open scoped BigOperators`):
--
--   ```lean
--   theorem condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss
--       {B : Type*} [mB : MeasurableSpace B] {Y : Ω → B} (hY : Measurable Y)
--       (hOwn : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le
--         Y (fun x i => X i x) rho)
--       (hOwnStrict : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mB.comap Y] x| < 1)
--       (hOwnSym : Measure.map (fun u : ℝ => -u)
--         (Measure.map (rho[fun y => spinSign (S y) | mB.comap Y]) rho) =
--           Measure.map (rho[fun y => spinSign (S y) | mB.comap Y]) rho)
--       {a b : ι} (hab : a ≠ b) {theta : ℝ}
--       (haTheta : ∀ᵐ x ∂rho,
--         |rho[fun y => spinSign (S y) | (mA a).comap (X a)] x| ≤ theta)
--       (hbTheta : ∀ᵐ x ∂rho,
--         |rho[fun y => spinSign (S y) | (mA b).comap (X b)] x| ≤ theta)
--       (htheta : theta < 1) :
--       (∫ x, (rho[fun y => spinSign (S y) |
--         (inferInstance : MeasurableSpace (B × (∀ i, A i))).comap
--           (fun x => (Y x, fun i => X i x))] x) ^ 2 ∂rho) ≤
--         (∫ x, (rho[fun y => spinSign (S y) | mB.comap Y] x) ^ 2 ∂rho) +
--         (∑ i, ∫ x, (rho[fun y => spinSign (S y) | (mA i).comap (X i)] x) ^ 2 ∂rho) -
--           2 * (1 - theta ^ 2) *
--             (∫ x, (rho[fun y => spinSign (S y) | (mA a).comap (X a)] x) ^ 2 ∂rho) *
--             (∫ x, (rho[fun y => spinSign (S y) | (mA b).comap (X b)] x) ^ 2 ∂rho)
--   ```
--
--   **Definitions.** The statement is written with `OAI.Problem367.spinSign` (definitions bundle `Q243FI000` of this split); `OAI.Problem367.IsingSpin` and `OAI.Problem367.isingSpinMeasurable` (the published bundle `Def_FreeIsing`).
--
--   **Used by.** The proofs of `OAI.Problem367.HasFreeIsingLaw.gaussianComponentField_critical_base_moments`, `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_tendsto_zero` and `OAI.Problem367.HasFreeIsingLaw.infiniteGibbsSpinMean_brownian_critical_zero` of this split import it.
-- source:
--   OpenAI, The sharp factor-of-IID threshold for the free Ising model on regular trees, OpenAI Math Release, September 26, 2026, https://github.com/openai/math (result family 236; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-sharp-factor-of-IID-threshold-for-the-free-Ising-model-on-regular-trees-September-26-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/FreeIsing/Conditioning/FiniteObservationInformation.lean (declaration OAI.Problem367.condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss)

import Mathlib
import Definitions.Def_FreeIsing
import Definitions.Def_Q243FI000

section

attribute [-instance] _root_.OAI.Problem367.IsingObservationInnovation.observationLaw_probability _root_.OAI.Problem367.WienerSampler.pathMeasurableSpace _root_.OAI.Problem367.reducedTailFinite _root_.OAI.Problem367.reducedTailFintype _root_.OAI.Problem367.treeBallFinite _root_.OAI.Problem367.treeBallFintype _root_.OAI.Problem367.treeShellFinite _root_.OAI.Problem367.treeShellFintype
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace Problem367

section Observations

variable {Ω ι : Type*} {A : ι → Type*} [mΩ : MeasurableSpace Ω]
  [StandardBorelSpace Ω] [mA : ∀ i, MeasurableSpace (A i)] [Fintype ι]
  {rho : Measure Ω} [IsProbabilityMeasure rho]
  {S : Ω → IsingSpin} (hS : Measurable S)
  {X : ∀ i, Ω → A i} (hX : ∀ i, Measurable (X i))
  (hCI : iCondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le X rho)
  (hfair : ∀ a : IsingSpin, rho {x | S x = a} = (1 / 2 : ENNReal))
  (hstrict : ∀ i, ∀ᵐ x ∂rho,
    |rho[fun y => spinSign (S y) | (mA i).comap (X i)] x| < 1)
  (hsym : ∀ i, Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | (mA i).comap (X i)]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | (mA i).comap (X i)]) rho)

include hS hX hCI hfair hstrict hsym

theorem condExp_own_and_finite_observation_secondMoment_le_sum_sub_loss
    {B : Type*} [mB : MeasurableSpace B] {Y : Ω → B} (hY : Measurable Y)
    (hOwn : CondIndepFun (MeasurableSpace.comap S inferInstance) hS.comap_le
      Y (fun x i => X i x) rho)
    (hOwnStrict : ∀ᵐ x ∂rho, |rho[fun y => spinSign (S y) | mB.comap Y] x| < 1)
    (hOwnSym : Measure.map (fun u : ℝ => -u)
      (Measure.map (rho[fun y => spinSign (S y) | mB.comap Y]) rho) =
        Measure.map (rho[fun y => spinSign (S y) | mB.comap Y]) rho)
    {a b : ι} (hab : a ≠ b) {theta : ℝ}
    (haTheta : ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA a).comap (X a)] x| ≤ theta)
    (hbTheta : ∀ᵐ x ∂rho,
      |rho[fun y => spinSign (S y) | (mA b).comap (X b)] x| ≤ theta)
    (htheta : theta < 1) :
    (∫ x, (rho[fun y => spinSign (S y) |
      (inferInstance : MeasurableSpace (B × (∀ i, A i))).comap
        (fun x => (Y x, fun i => X i x))] x) ^ 2 ∂rho) ≤
      (∫ x, (rho[fun y => spinSign (S y) | mB.comap Y] x) ^ 2 ∂rho) +
      (∑ i, ∫ x, (rho[fun y => spinSign (S y) | (mA i).comap (X i)] x) ^ 2 ∂rho) -
        2 * (1 - theta ^ 2) *
          (∫ x, (rho[fun y => spinSign (S y) | (mA a).comap (X a)] x) ^ 2 ∂rho) *
          (∫ x, (rho[fun y => spinSign (S y) | (mA b).comap (X b)] x) ^ 2 ∂rho) := by
  sorry

end Observations

end Problem367

end

end OAI
end
