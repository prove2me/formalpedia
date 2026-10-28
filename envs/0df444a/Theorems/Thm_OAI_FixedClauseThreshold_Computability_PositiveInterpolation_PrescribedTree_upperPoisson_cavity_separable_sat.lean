-- Prove2me | Theorems.Thm_OAI_FixedClauseThreshold_Computability_PositiveInterpolation_PrescribedTree_upperPoisson_cavity_separable_sat
-- name    : OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable_sat
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:22:57.63335+00:00
-- url     : https://prove2.me/theorems/37a820ab-8dc2-4bc4-a57f-c058040f7c5c
-- title:
--   OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable_sat (OpenAI intermediate lemma)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.FixedClauseThreshold.Computability.main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Limiting random SAT thresholds, sharp variance and computability (result family 235)*, OpenAI Math Release, September 27, 2026, result family 235, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable` of [lean/OAI/Probability/SATComputability/InterpolationUpper.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/InterpolationUpper.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree`, with `open DilutedSpinGlass DilutedSpinGlass.PrescribedTree DilutedSpinGlass.KernelTower`, `open _root_.MeasureTheory ProbabilityTheory Filter Set`, `open scoped BigOperators NNReal ENNReal Topology`):
--
--   ```lean
--   lemma upperPoisson_cavity_separable_sat (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
--       (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
--       (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
--       (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
--       (f : Fin N → FinitePath Ω n → ℝ) (r : ℝ≥0) :
--       (∫ l,upperCountMean M (KernelTower.pi n T) Q U (fun y s => V s (FinitePath.proj n y s)) x m j
--         (fun y => ∑ s,f s (FinitePath.proj n y s)) 0 l ∂poissonMeasure r)=
--         ∑ s : Fin N,∫ k,activeCountMean M Q (T s) U (V s) x m j (f s) k
--           ∂poissonMeasure (r/N)
--   ```
--
--   **Definitions.** The statement is written with `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.InterpolationAdmissible` (definitions bundle `OAIQ067A001` of this split); `OAI.DilutedSpinGlass.Model` and `OAI.DilutedSpinGlass.Spin` (the published bundle `Def_DilutedSpin`); `OAI.DilutedSpinGlass.FiniteLaw`, `OAI.DilutedSpinGlass.FinitePath`, `OAI.DilutedSpinGlass.KernelTower`, `OAI.DilutedSpinGlass.FinitePath.proj`, `OAI.DilutedSpinGlass.KernelTower.pi`, `OAI.DilutedSpinGlass.PrescribedTree.activeCountMean` and `OAI.DilutedSpinGlass.PrescribedTree.upperCountMean` (the published bundle `Def_OAIQ041D000`).
--
--   **Used by.** The proof of `OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.finiteTrial_upper_fixedField_sat` of this split imports it.
-- source:
--   OpenAI, Limiting random SAT thresholds, sharp variance and computability (result family 235), OpenAI Math Release, September 27, 2026, https://github.com/openai/math (result family 235; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Computing-the-Random-3-SAT-Threshold-September-27-2026/article.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/Probability/SATComputability/InterpolationUpper.lean (declaration OAI.FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree.upperPoisson_cavity_separable)

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

lemma upperPoisson_cavity_separable_sat (M : Model p) (hM : InterpolationAdmissible M) (Q : FiniteLaw R)
    (T : Fin N → KernelTower Ω n) (U : R → KernelTower Λ n)
    (V : Fin N → FinitePath Ω n → Spin) (x : R → FinitePath Λ n → ℝ)
    (m : Fin n → ℝ) (hm : ∀ d,0 < m d) (j : Fin p)
    (f : Fin N → FinitePath Ω n → ℝ) (r : ℝ≥0) :
    (∫ l,upperCountMean M (KernelTower.pi n T) Q U (fun y s => V s (FinitePath.proj n y s)) x m j
      (fun y => ∑ s,f s (FinitePath.proj n y s)) 0 l ∂poissonMeasure r)=
      ∑ s : Fin N,∫ k,activeCountMean M Q (T s) U (V s) x m j (f s) k
        ∂poissonMeasure (r/N) := by
  sorry

end
end FixedClauseThreshold.Computability.PositiveInterpolation.PrescribedTree

end

end OAI
end
