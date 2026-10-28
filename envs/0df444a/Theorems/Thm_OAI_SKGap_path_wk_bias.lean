-- Prove2me | Theorems.Thm_OAI_SKGap_path_wk_bias
-- name    : OAI.SKGap.path_wk_bias
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T06:24:38.776882+00:00
-- url     : https://prove2.me/theorems/5fdd2a86-794a-45d4-a467-fd6afa196045
-- title:
--   OAI.SKGap.path_wk_bias: intermediate lemma from OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.SKGap.sk_main`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227)*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.SKGap.path_wk_bias` of [lean/OAI/Probability/SKGap/Brownian/PathBias.lean](https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Brownian/PathBias.lean) at commit 1581d4c, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix MeasureTheory ProbabilityTheory Real Set`, `open RealComplex`, `open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap`):
--
--   ```lean
--   lemma path_wk_bias (f : 𝓢(ℝ,ℂ)) {lo hi R j A rate z ε : ℝ} {a : ι → ℝ}
--       (hlo : 0 < lo) (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
--       (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A) (hrate : 0 < rate) (hε : 0 ≤ ε)
--       (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1)
--       (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
--         (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi (pathDiagonal a z)
--           (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)))ᶜ ≤
--             3*Real.exp (-rate*(Fintype.card ι:ℝ)))
--       (hk : ∀ i, |pathExpected f R hR j a z i-1| ≤ ε) (i : ι) :
--       |pathExpectedWK f R hR j a z i-z*((j/(Fintype.card ι:ℝ))*∑ b, a b)| ≤
--         loopErrorConstantOne j A (pathBound f R j A) (pathLip f R j A) rate/(Fintype.card ι:ℝ)+
--           j*A*ε*(pathBound f R j A+1)
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.loopErrorConstantOne`, `OAI.SKGap.pathBound`, `OAI.SKGap.pathDiagonal`, `OAI.SKGap.pathExpected`, `OAI.SKGap.pathExpectedWK`, `OAI.SKGap.pathLip`, `OAI.SKGap.pathShift` and `OAI.SKGap.truncationGoodSet` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** The proof of `OAI.SKGap.actual_projected_path_equivalents` of this split imports it.
-- source:
--   OpenAI, A spectral gap throughout the high-temperature Sherrington-Kirkpatrick phase (result family 227), OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/preprints/A-spectral-gap-throughout-the-high-temperature-Sherrington-Kirkpatrick-phase-September-24-2026/main.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/SKGap/Brownian/PathBias.lean (declaration OAI.SKGap.path_wk_bias)

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

lemma path_wk_bias (f : 𝓢(ℝ,ℂ)) {lo hi R j A rate z ε : ℝ} {a : ι → ℝ}
    (hlo : 0 < lo) (hf : ∀ x ∈ Icc lo hi, f x = (x : ℂ)⁻¹)
    (hR : 0 ≤ R) (hj : 0 ≤ j) (hA0 : 0 ≤ A) (hrate : 0 < rate) (hε : 0 ≤ ε)
    (ha : ∀ i, 0 ≤ a i) (hA : ∀ i, a i ≤ A) (hz : z ∈ Icc (0:ℝ) 1)
    (hp : (Measure.pi (fun _ : MatrixCoordinates ι => gaussianReal 0 1)).real
      (truncationGoodSet (j/(Fintype.card ι:ℝ)) R lo hi (pathDiagonal a z)
        (pathShift z ((j/(Fintype.card ι:ℝ))*∑ b, a b)))ᶜ ≤
          3*Real.exp (-rate*(Fintype.card ι:ℝ)))
    (hk : ∀ i, |pathExpected f R hR j a z i-1| ≤ ε) (i : ι) :
    |pathExpectedWK f R hR j a z i-z*((j/(Fintype.card ι:ℝ))*∑ b, a b)| ≤
      loopErrorConstantOne j A (pathBound f R j A) (pathLip f R j A) rate/(Fintype.card ι:ℝ)+
        j*A*ε*(pathBound f R j A+1) := by
  sorry
end SKGap
end
end

end OAI
end
