-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_finiteTrial_upper_fixedField_sat
-- name    : OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:22:14.611764+00:00
-- url     : https://prove2.me/theorems/47c86508-0a25-4de3-a2a4-0c5377e1709d
-- title:
--   OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField` of [lean/OAI/Probability/SATComputability/InterpolationUpper.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/InterpolationUpper.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree`, with `open DilutedSpinGlass DilutedSpinGlass.PrescribedTree DilutedSpinGlass.KernelTower`, `open _root_.MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators NNReal ENNReal Topology`):
--
--   ```lean
--   lemma finiteTrial_upper_fixedField_sat (M : Model (q+1)) (hM : InterpolationAdmissible M)
--       (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
--       (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (hm : Exponents m) (h : Fin N → ℝ) :
--       (∫ k,∫ z : Fin k → InteractionSample (q+1),
--         (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (q+1) → Fin N)).expect
--           (fun i => logPartition z h i-(N:ℝ)*Real.log 2)
--         ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*N))+
--         (M.alpha:ℝ)*N*q*(∫ z,trialLog r (finiteTrialLaw r Q U x) m
--           (fun y => Real.log (edge z.1 y)) ∂M.disorder.toMeasure) ≤
--         ∑ s : Fin N,∫ k,∫ z : Fin k → InteractionSample (q+1),
--           trialLog r (finiteTrialLaw r Q U x) m (siteLog z (h s))
--           ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*(q+1))
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.InterpolationAdmissible` (definitions bundle `OAIQ067A001` of this split); `OAI.DilutedSpinGlass.Exponents`, `OAI.DilutedSpinGlass.Interaction`, `OAI.DilutedSpinGlass.InteractionSample`, `OAI.DilutedSpinGlass.Model`, `OAI.DilutedSpinGlass.Spin`, `OAI.DilutedSpinGlass.edge`, `OAI.DilutedSpinGlass.logPartition`, `OAI.DilutedSpinGlass.siteLog` and `OAI.DilutedSpinGlass.trialLog` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.FiniteLaw.expect`, `OAI.DilutedSpinGlass.FiniteLaw.uniform` and `OAI.DilutedSpinGlass.PrescribedTree.finiteTrialLaw` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proofs of `OAI.FixedClauseThreshold.Computability.negative_pressure_of_violation_density_sat` and `OAI.FixedClauseThreshold.Computability.satTrialEvaluation_sound_sat` of this split import it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/InterpolationUpper.lean (declaration OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000
import Definitions.Def_OAIQ067A001

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section
open DilutedSpinGlass DilutedSpinGlass.PrescribedTree DilutedSpinGlass.KernelTower
open _root_.MeasureTheory ProbabilityTheory Filter Set
open scoped BigOperators NNReal ENNReal Topology

namespace FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree
section
variable {Ω Λ R : Type} [Fintype Ω] [Fintype Λ] [Fintype R]
  [MeasurableSpace R] [MeasurableSingletonClass R]
  {n p N q : ℕ} [NeZero N]

lemma finiteTrial_upper_fixedField_sat (M : Model (q+1)) (hM : InterpolationAdmissible M)
    (a : Λ) (r : ℕ) (Q : FiniteLaw R) (U : R → KernelTower Λ r)
    (x : R → FinitePath Λ r → ℝ) (m : Fin r → ℝ) (hm : Exponents m) (h : Fin N → ℝ) :
    (∫ k,∫ z : Fin k → InteractionSample (q+1),
      (FiniteLaw.uniform : FiniteLaw (Fin k → Fin (q+1) → Fin N)).expect
        (fun i => logPartition z h i-(N:ℝ)*Real.log 2)
      ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*N))+
      (M.alpha:ℝ)*N*q*(∫ z,trialLog r (finiteTrialLaw r Q U x) m
        (fun y => Real.log (edge z.1 y)) ∂M.disorder.toMeasure) ≤
      ∑ s : Fin N,∫ k,∫ z : Fin k → InteractionSample (q+1),
        trialLog r (finiteTrialLaw r Q U x) m (siteLog z (h s))
        ∂Measure.pi (fun _ : Fin k => M.disorder.toMeasure) ∂poissonMeasure (M.alpha*(q+1)) := by
  sorry

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

end

end OAI
end
