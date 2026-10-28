-- Prove2me | Theorems.Thm_OAI_CoulombAtom_normalized_inner_event_global_bound
-- name    : OAI.CoulombAtom.normalized_inner_event_global_bound
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T05:27:57.227963+00:00
-- url     : https://prove2.me/theorems/2761984a-64a9-4736-b37e-17f08fdfaa39
-- title:
--   OAI.CoulombAtom.normalized_inner_event_global_bound: intermediate lemma from OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CoulombAtom.generalized_ionization`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Generalized ionization energies for full Coulomb atoms (result family 263)*, OpenAI Math Release, September 24, 2026, result family 263, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CoulombAtom.normalized_inner_event_global_bound` of [lean/OAI/Analysis/CoulombIonization/Ionization/BarrierInitialEventBarrier.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Ionization/BarrierInitialEventBarrier.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CoulombAtom`, with `open MeasureTheory Filter`, `open scoped Topology BigOperators ContDiff`, `open MeasureTheory Filter Set Metric`, `open scoped BigOperators ENNReal ContDiff`, `open CoulombAnalysis`):
--
--   ```lean
--   theorem normalized_inner_event_global_bound {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
--       {ψ : FormVector N} (hψ : FormAdmissible ψ)
--       (ell : Fin K → ℝ) (j : ℕ) (y : Space)
--       (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
--       {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
--       {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
--       (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
--       (hy : ‖y‖ ≤ (11/10)*r₀)
--       {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
--       (hA : MeasurableSet[observationInformation ell j] A) {p : ℝ} (hp : 0 < p)
--       (hlaw : formRawLaw ψ = (ENNReal.ofReal p)⁻¹ • Measure.map Prod.fst ((physicalObservationLaw μ K).restrict A))
--       {Z δ : ℝ} (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hN : (N:ℝ) ≤ 3*Z)
--       (hE : formEnergy Z ψ ≤ allSectorEnergy Z+δ) :
--       p⁻¹*(∫ z in A, innerPotential r₀ (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
--         ∂physicalObservationLaw μ K) ≤
--         (Pauli.globalDensityConstant*(Z^(7/3:ℝ)+δ))^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CoulombAnalysis.IsRadial` (definitions bundle `OAIQ071C000` of this split); `OAI.CoulombAtom.allSectorEnergy` and `OAI.CoulombAtom.Pauli.globalDensityConstant` (definitions bundle `OAIQ071C002` of this split); `OAI.CoulombAtom.formRawLaw` (definitions bundle `OAIQ071C004` of this split); `OAI.CoulombAtom.jointMasterPosterior`, `OAI.CoulombAtom.observationInformation`, `OAI.CoulombAtom.originalDatum`, `OAI.CoulombAtom.physicalObservationLaw` and `OAI.CoulombAtom.rawPotential` (definitions bundle `OAIQ071C006` of this split); `OAI.CoulombAtom.innerPotential` (definitions bundle `OAIQ071C009` of this split); `OAI.CoulombAtom.Configuration`, `OAI.CoulombAtom.FormAdmissible`, `OAI.CoulombAtom.FormVector`, `OAI.CoulombAtom.Space` and `OAI.CoulombAtom.formEnergy` (the published bundle `Def_CoulombIonization`).
--
--   **Used by.** The proofs of `OAI_CoulombBarrier_own_state_initial_barrier` and `OAI.CoulombBarrier.tail_initial_good_event` of this split import it.
-- source:
--   OpenAI, Generalized ionization energies for full Coulomb atoms (result family 263), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 263; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Generalized-ionization-energies-for-full-Coulomb-atoms-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Analysis/CoulombIonization/Ionization/BarrierInitialEventBarrier.lean (declaration OAI.CoulombAtom.normalized_inner_event_global_bound)

import Mathlib
import Definitions.Def_CoulombIonization
import Definitions.Def_OAIQ071C009

section

attribute [-instance] _root_.OAI.CoulombAtom.rotationMeasureHaar
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

namespace CoulombAtom

open MeasureTheory Filter
open scoped Topology BigOperators ContDiff

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis

theorem normalized_inner_event_global_bound {N K : ℕ} (μ : Measure (Configuration N)) [IsFiniteMeasure μ]
    {ψ : FormVector N} (hψ : FormAdmissible ψ)
    (ell : Fin K → ℝ) (j : ℕ) (y : Space)
    (hi : Integrable (rawPotential y) μ) (he : ∀ᵐ x ∂μ, ∀ i, x i ≠ y)
    {c₁ r₀ s : ℝ} (hc : 0 < c₁) (hc1 : c₁ ≤ 1/2) (hr : 0 < r₀) (hs : 0 < s) (hs1 : s ≤ 1)
    {g : Space → ℝ} (hg : ContDiff ℝ ∞ g) (hcg : HasCompactSupport g)
    (hgn : ∫ z, (g z)^2 = 1) (hrad : IsRadial g) (hgs : tsupport g ⊆ ball 0 1)
    (hy : ‖y‖ ≤ (11/10)*r₀)
    {A : Set (Configuration N × (Fin K × (Fin N × Fin 3) → ℝ))}
    (hA : MeasurableSet[observationInformation ell j] A) {p : ℝ} (hp : 0 < p)
    (hlaw : formRawLaw ψ = (ENNReal.ofReal p)⁻¹ • Measure.map Prod.fst ((physicalObservationLaw μ K).restrict A))
    {Z δ : ℝ} (hZ : 1 ≤ Z) (hδ : 0 ≤ δ) (hN : (N:ℝ) ≤ 3*Z)
    (hE : formEnergy Z ψ ≤ allSectorEnergy Z+δ) :
    p⁻¹*(∫ z in A, innerPotential r₀ (jointMasterPosterior μ ell j c₁ r₀ s g (originalDatum ell j z)) y
      ∂physicalObservationLaw μ K) ≤
      (Pauli.globalDensityConstant*(Z^(7/3:ℝ)+δ))^(3/5:ℝ)*(8*Real.pi)^(2/5:ℝ)*(4*r₀)^(1/5:ℝ) := by
  sorry

open MeasureTheory Filter Set Metric
open scoped BigOperators ENNReal ContDiff

open CoulombAnalysis CoulombObservation
attribute [local irreducible] graphComponent graphFormVector fermionGraph weakGraph fermionGraphValue

end CoulombAtom

end

end OAI
end
