-- Prove2me | Theorems.Thm_OAI_SphericalPerceptronFreeEnergy_source_contact_joint_gg_rate
-- name    : OAI.SphericalPerceptronFreeEnergy.source_contact_joint_gg_rate
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T22:14:59.798237+00:00
-- url     : https://prove2.me/theorems/71c5d26d-486e-47ed-96f9-3731e7187b67
-- title:
--   OAI.SphericalPerceptronFreeEnergy.source_contact_joint_gg_rate: intermediate lemma from OpenAI, Spherical perceptron free energy (OpenAI result family 222)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SphericalPerceptronFreeEnergy.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Spherical perceptron free energy (OpenAI result family 222)*, OpenAI Math Release, September 24, 2026, result family 222, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SphericalPerceptronFreeEnergy.source_contact_joint_gg_rate` of [lean/OAI/Probability/Perceptron/Variational/ContactGGRate.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/ContactGGRate.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SphericalPerceptronFreeEnergy`, with `open Filter MeasureTheory ProbabilityTheory Set`, `open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Classical`):
--
--   ```lean
--   lemma source_contact_joint_gg_rate (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
--       (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
--       (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (z : Fin k → ℝ) (hz : StrictMono z)
--       (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
--       {H T c a s : ℝ} (hH : 0 ≤ H) (hhH : h 0 ≤ H) (ht : (t:ℝ) ≤ T) (hs : 0 < s)
--       (hu : ∀ l, u l ∈ Icc 1 2)
--       (hup : ∀ l, (u+Pi.single j s : Fin (n+1) → ℝ) l ∈ Icc 1 2) (hum : ∀ l, (u+Pi.single j (-s) : Fin (n+1) → ℝ) l ∈ Icc 1 2)
--       (hmin : IsLocalMin (fun r => c*(r-a)^2-
--         ∫ b, sourceKernelPressure n k f p d (u+Pi.single j r) h b
--           ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) 0)
--       (hp : c*(0-a)^2-(∫ b, sourceKernelPressure n k f p d u h b
--         ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤ c*(s-a)^2-
--         ∫ b, sourceKernelPressure n k f p d (u+Pi.single j s) h b
--           ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw)
--       (hm : c*(0-a)^2-(∫ b, sourceKernelPressure n k f p d u h b
--         ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤ c*(-s-a)^2-
--         ∫ b, sourceKernelPressure n k f p d (u+Pi.single j (-s)) h b
--           ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw)
--       (r : ℕ) (i : Fin r) {G : (Fin r → NormalizedSpin (n+1)×IndexedLeaf k) → ℝ}
--       (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B)
--       (hc0 : 0 ≤ c) (hsdef : s=(n+1:ℕ)^(-(1:ℝ)/4)) :
--       |kernelGGDefect (sourceFullSpinLeafKernel n k)
--         ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
--         (sourceCouplingHamiltonian n k f p d h u) (sourceJointMonomial p d j)
--         (((k:ℝ)/(k+1:ℕ))^(d j)) r i G| ≤
--         B/(((2:ℝ)^(-((j.val+1:ℕ):ℤ)))^2)*
--           (Real.sqrt (2*c)*(n+1:ℕ)^(-(3:ℝ)/8)+
--             (c+4*Real.sqrt (enrichedVarianceConstant k z f H T))*(n+1:ℕ)^(-(1:ℝ)/8))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SphericalPerceptronFreeEnergy.IndexedCascadeBase`, `OAI.SphericalPerceptronFreeEnergy.IndexedLeaf`, `OAI.SphericalPerceptronFreeEnergy.NormalizedSpin`, `OAI.SphericalPerceptronFreeEnergy.SourceBaseData`, `OAI.SphericalPerceptronFreeEnergy.countableGaussianLaw`, `OAI.SphericalPerceptronFreeEnergy.enrichedVarianceConstant`, `OAI.SphericalPerceptronFreeEnergy.kernelGGDefect`, `OAI.SphericalPerceptronFreeEnergy.sourceBaseDataLaw` and `OAI.SphericalPerceptronFreeEnergy.sourceFullSpinLeafKernel` (definitions bundle `OAIQ61Pf000` of this split); `OAI.SphericalPerceptronFreeEnergy.sourceCouplingHamiltonian`, `OAI.SphericalPerceptronFreeEnergy.sourceJointMonomial` and `OAI.SphericalPerceptronFreeEnergy.sourceKernelPressure` (definitions bundle `OAIQ61Pf002` of this split); `OAI.SphericalPerceptronFreeEnergy.Spin` (the published bundle `Def_PerceptronFreeEnergy`).
--
--   **Used by.** The proof of `OAI.SphericalPerceptronFreeEnergy.source_contact_monomial_tendsto` of this split imports it.
-- source:
--   OpenAI, Spherical perceptron free energy (OpenAI result family 222), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 222; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/PerceptronFreeEnergy.lean; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/Perceptron/Variational/ContactGGRate.lean (declaration OAI.SphericalPerceptronFreeEnergy.source_contact_joint_gg_rate)

import Mathlib
import Definitions.Def_PerceptronFreeEnergy
import Definitions.Def_OAIQ61Pf002

section

attribute [-instance] _root_.OAI.SphericalPerceptronFreeEnergy.bulkFiniteReplicaLaw_probability _root_.OAI.SphericalPerceptronFreeEnergy.bulkSpinKernel_markov _root_.OAI.SphericalPerceptronFreeEnergy.cavityIndexMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.finiteSigmaMeasurableSingleton _root_.OAI.SphericalPerceptronFreeEnergy.indexedInfiniteLeafMeasure_probability _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelProdCarrierIndexedCascadeBaseIndexedCascadeMarksIndexedLeafIndexedTerminalBaseKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsMarkovKernelSourceCountDataProdElemSpinHAddNatOfNatNormalizedSpinCarrierIndexedLeafSourceCountKernel _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityIncrementRandomCavityIncrementLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureCavityProxyRandomCavityProxyLaw _root_.OAI.SphericalPerceptronFreeEnergy.instIsProbabilityMeasureSourceCountDataSourceCountLaw _root_.OAI.SphericalPerceptronFreeEnergy.unitSphereAmbientLaw_probability
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
namespace SphericalPerceptronFreeEnergy
open Filter MeasureTheory ProbabilityTheory Set
open scoped Topology NNReal ENNReal BigOperators BoundedContinuousFunction Classical

lemma source_contact_joint_gg_rate (n k : ℕ) (f : ℝ →ᵇ ℝ) (p d : Fin (n+1) → ℕ)
    (h : Fin (k+1) → ℝ) (hh0 : ∀ l, 0 ≤ h l) (hh : Monotone h)
    (u : Fin (n+1) → ℝ) (j : Fin (n+1)) (z : Fin k → ℝ) (hz : StrictMono z)
    (hz0 : ∀ i, 0<z i) (hz1 : ∀ i, z i<1) (t : ℝ≥0)
    {H T c a s : ℝ} (hH : 0 ≤ H) (hhH : h 0 ≤ H) (ht : (t:ℝ) ≤ T) (hs : 0 < s)
    (hu : ∀ l, u l ∈ Icc 1 2)
    (hup : ∀ l, (u+Pi.single j s : Fin (n+1) → ℝ) l ∈ Icc 1 2) (hum : ∀ l, (u+Pi.single j (-s) : Fin (n+1) → ℝ) l ∈ Icc 1 2)
    (hmin : IsLocalMin (fun r => c*(r-a)^2-
      ∫ b, sourceKernelPressure n k f p d (u+Pi.single j r) h b
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) 0)
    (hp : c*(0-a)^2-(∫ b, sourceKernelPressure n k f p d u h b
      ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤ c*(s-a)^2-
      ∫ b, sourceKernelPressure n k f p d (u+Pi.single j s) h b
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (hm : c*(0-a)^2-(∫ b, sourceKernelPressure n k f p d u h b
      ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw) ≤ c*(-s-a)^2-
      ∫ b, sourceKernelPressure n k f p d (u+Pi.single j (-s)) h b
        ∂(sourceBaseDataLaw n k z t).prod countableGaussianLaw)
    (r : ℕ) (i : Fin r) {G : (Fin r → NormalizedSpin (n+1)×IndexedLeaf k) → ℝ}
    (hG : Measurable G) {B : ℝ} (hB : 0 ≤ B) (hGB : ∀ x, |G x| ≤ B)
    (hc0 : 0 ≤ c) (hsdef : s=(n+1:ℕ)^(-(1:ℝ)/4)) :
    |kernelGGDefect (sourceFullSpinLeafKernel n k)
      ((sourceBaseDataLaw n k z t).prod countableGaussianLaw)
      (sourceCouplingHamiltonian n k f p d h u) (sourceJointMonomial p d j)
      (((k:ℝ)/(k+1:ℕ))^(d j)) r i G| ≤
      B/(((2:ℝ)^(-((j.val+1:ℕ):ℤ)))^2)*
        (Real.sqrt (2*c)*(n+1:ℕ)^(-(3:ℝ)/8)+
          (c+4*Real.sqrt (enrichedVarianceConstant k z f H T))*(n+1:ℕ)^(-(1:ℝ)/8)) := by
  sorry

end SphericalPerceptronFreeEnergy

end

end OAI
end
