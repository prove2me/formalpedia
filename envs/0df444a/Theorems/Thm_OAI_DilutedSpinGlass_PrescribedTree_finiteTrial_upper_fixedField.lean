-- Prove2me | Theorems.Thm_OAI_DilutedSpinGlass_PrescribedTree_finiteTrial_upper_fixedField
-- name    : OAI.DilutedSpinGlass.PrescribedTree.finiteTrial_upper_fixedField
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-27T07:56:12.229295+00:00
-- url     : https://prove2.me/theorems/96d7aff7-14b0-443e-a7e1-2804a66a26ae
-- title:
--   OAI.DilutedSpinGlass.PrescribedTree.finiteTrial_upper_fixedField: intermediate lemma from OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.DilutedSpinGlass.mezard_parisi`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *The Mézard–Parisi formula for diluted spin glasses (result family 221)*, OpenAI Math Release, September 23, 2026, result family 221, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.DilutedSpinGlass.PrescribedTree.finiteTrial_upper_fixedField` of [lean/OAI/Probability/DilutedSpin/DilutedSpin/CavityGapFubini.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/CavityGapFubini.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.DilutedSpinGlass.PrescribedTree`, with `open _root_.MeasureTheory ProbabilityTheory KernelTower`, `open scoped BigOperators NNReal`):
--
--   ```lean
--   lemma finiteTrial_upper_fixedField (M : Model (q+1)) (hM : Admissible M)
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
--   **Definitions.** The statement is written with `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.FiniteLaw.expect`, `OAI.DilutedSpinGlass.FiniteLaw.uniform` and `OAI.DilutedSpinGlass.PrescribedTree.finiteTrialLaw` (definitions bundle `OAIQ041D000` of this split); `OAI.DilutedSpinGlass.Admissible`, `OAI.DilutedSpinGlass.Exponents`, `OAI.DilutedSpinGlass.Interaction`, `OAI.DilutedSpinGlass.InteractionSample`, `OAI.DilutedSpinGlass.Model`, `OAI.DilutedSpinGlass.Spin`, `OAI.DilutedSpinGlass.edge`, `OAI.DilutedSpinGlass.logPartition`, `OAI.DilutedSpinGlass.siteLog` and `OAI.DilutedSpinGlass.trialLog` (the published bundle `Def_DilutedSpin`).
--
--   **Used by.** The proof of `OAI.DilutedSpinGlass.mezard_parisi` of this split imports it.
-- source:
--   OpenAI, The Mézard–Parisi formula for diluted spin glasses (result family 221), OpenAI Math Release, September 23, 2026, https://github.com/openai/math (result family 221; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/The-Mezard-Parisi-formula-for-diluted-spin-glasses-September-23-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/DilutedSpin/DilutedSpin/CavityGapFubini.lean (declaration OAI.DilutedSpinGlass.PrescribedTree.finiteTrial_upper_fixedField)

import Mathlib
import Definitions.Def_DilutedSpin
import Definitions.Def_OAIQ041D000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
namespace DilutedSpinGlass.PrescribedTree
open _root_.MeasureTheory ProbabilityTheory KernelTower
open scoped BigOperators NNReal
variable {Λ R : Type} [Fintype Λ] [Fintype R]
    [MeasurableSpace R] [MeasurableSingletonClass R] {N q : ℕ} [NeZero N]

lemma finiteTrial_upper_fixedField (M : Model (q+1)) (hM : Admissible M)
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

end DilutedSpinGlass.PrescribedTree

end

end OAI
end
