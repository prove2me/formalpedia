-- Prove2me | Theorems.Thm_OAI_SKGap_path_self_consistency
-- name    : OAI.SKGap.path_self_consistency
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:24:20.622379+00:00
-- url     : https://prove2.me/theorems/e5332e80-530a-4b81-a2ca-f32219448515
-- title:
--   OAI.SKGap.path_self_consistency: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.path_self_consistency` of [lean/OAI/Probability/SKGap/Brownian/PathExpectation.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Brownian/PathExpectation.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix MeasureTheory ProbabilityTheory Real Set`, `open RealComplex`, `open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap`):
--
--   ```lean
--   lemma path_self_consistency (f : 𝓢(ℝ,ℂ)) {lo hi R j A rate z : ℝ} {a : ι → ℝ}
--       (hlo : 0 < lo) (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
--       (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A) (hrate : 0 < rate)
--       (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1)
--       (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
--         (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi (pathDiagonal a z)
--           (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)))ᶜ ≤
--             3*Real.exp (-rate*(Fintype.card ι:ℝ))) (i : ι) :
--       let k := pathExpected f R hR j a z
--       let B := pathBound f R j A
--       let L := pathLip f R j A
--       |k i-1-z^2*j*a i*(∑ b, (1/(Fintype.card ι:ℝ))*a b*(k b-1))*k i| ≤
--         (loopErrorConstantTwo j A B rate+A*loopErrorConstantOne j A B L rate)/(Fintype.card ι:ℝ)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.loopErrorConstantOne`, `OAI.SKGap.loopErrorConstantTwo`, `OAI.SKGap.pathBound`, `OAI.SKGap.pathDiagonal`, `OAI.SKGap.pathExpected`, `OAI.SKGap.pathLip`, `OAI.SKGap.pathShift` and `OAI.SKGap.truncationGoodSet` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proofs of `OAI.SKGap.actual_path_bias` and `OAI.SKGap.actual_word_simultaneous_prediction_of_cutoff` of this split import it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Brownian/PathExpectation.lean (declaration OAI.SKGap.path_self_consistency)

import Mathlib
import Definitions.Def_OAIQ072A000

section

set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

section
noncomputable section
namespace SKGap
open Matrix MeasureTheory ProbabilityTheory Real Set
open RealComplex
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma path_self_consistency (f : 𝓢(ℝ,ℂ)) {lo hi R j A rate z : ℝ} {a : ι → ℝ}
    (hlo : 0 < lo) (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A) (hrate : 0 < rate)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1)
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi (pathDiagonal a z)
        (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)))ᶜ ≤
          3*Real.exp (-rate*(Fintype.card ι:ℝ))) (i : ι) :
    let k := pathExpected f R hR j a z
    let B := pathBound f R j A
    let L := pathLip f R j A
    |k i-1-z^2*j*a i*(∑ b, (1/(Fintype.card ι:ℝ))*a b*(k b-1))*k i| ≤
      (loopErrorConstantTwo j A B rate+A*loopErrorConstantOne j A B L rate)/(Fintype.card ι:ℝ) := by
  sorry
end SKGap
end
end

end OAI
end
