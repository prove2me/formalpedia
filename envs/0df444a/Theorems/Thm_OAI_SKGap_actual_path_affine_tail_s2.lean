-- Prove2me | Theorems.Thm_OAI_SKGap_actual_path_affine_tail_s2
-- name    : OAI.SKGap.actual_path_affine_tail_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:47:46.424347+00:00
-- url     : https://prove2.me/theorems/0996e653-8b3a-4a8f-a7dd-011009f75f70
-- title:
--   OAI.SKGap.actual_path_affine_tail_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0), ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.SKGap`, with `open Matrix MeasureTheory ProbabilityTheory Real Set`, `open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap`):
--
--   ```lean
--   theorem actual_path_affine_tail_s2 {j A D U W ε : ℝ}
--       (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1)
--       (hD : 0 ≤ D) (hU : 0 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) :
--       ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (lo hi c : ℝ) (N : ℕ),
--         R=2*sqrt j+1+1 ∧ lo=(1-sqrt j*A)^2/4 ∧ hi=2+A*(2*sqrt j+1+j*A) ∧
--         0 < lo ∧ (∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) ∧ 0 < c ∧ 0 < N ∧
--         ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ A) →
--         ∀ (p : Bool) (d e : Fin n → ℝ) (w : ℝ), (∀ i, |d i| ≤ D) → |w| ≤ W →
--         ∀ (u v : EuclideanSpace ℝ (Fin n)), ‖u‖ ≤ U → ‖v‖ ≤ U →
--         (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
--           {g | ε ≤ |matrixBilinear (affineRight (pathFeature p f R hR j a) d e w
--             (goeMatrix (j/(n:ℝ)) g)-diagonal (fun i =>
--               (if p then (j/(n:ℝ))*∑ b,a b else 1)*d i-e i)) u v|} ≤ 2*exp (-c*(n:ℝ))
--   ```
--
--   **Definitions.** The statement is written with `OAI.SKGap.MatrixCoordinates`, `OAI.SKGap.affineRight`, `OAI.SKGap.goeMatrix`, `OAI.SKGap.matrixBilinear` and `OAI.SKGap.pathFeature` (definitions bundle `OAIQ072A000` of this split).
--
--   **Used by.** No other item of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0)

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
open scoped BigOperators Matrix.Norms.Frobenius NNReal ENNReal SchwartzMap
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem actual_path_affine_tail_s2 {j A D U W ε : ℝ}
    (hj : 0 < j) (hA : 0 < A) (hs : sqrt j*A < 1)
    (hD : 0 ≤ D) (hU : 0 ≤ U) (hW : 0 ≤ W) (hε : 0 < ε) :
    ∃ (f : 𝓢(ℝ,ℂ)) (R : ℝ) (hR : 0 ≤ R) (lo hi c : ℝ) (N : ℕ),
      R=2*sqrt j+1+1 ∧ lo=(1-sqrt j*A)^2/4 ∧ hi=2+A*(2*sqrt j+1+j*A) ∧
      0 < lo ∧ (∀ x ∈ Icc lo hi, f x=(x:ℂ)⁻¹) ∧ 0 < c ∧ 0 < N ∧
      ∀ n, N ≤ n → ∀ a : Fin n → ℝ, (∀ i, 0 ≤ a i) → (∀ i, a i ≤ A) →
      ∀ (p : Bool) (d e : Fin n → ℝ) (w : ℝ), (∀ i, |d i| ≤ D) → |w| ≤ W →
      ∀ (u v : EuclideanSpace ℝ (Fin n)), ‖u‖ ≤ U → ‖v‖ ≤ U →
      (Measure.pi (fun _ : MatrixCoordinates (Fin n) => gaussianReal 0 1)).real
        {g | ε ≤ |matrixBilinear (affineRight (pathFeature p f R hR j a) d e w
          (goeMatrix (j/(n:ℝ)) g)-diagonal (fun i =>
            (if p then (j/(n:ℝ))*∑ b,a b else 1)*d i-e i)) u v|} ≤ 2*exp (-c*(n:ℝ)) := by
  sorry
end SKGap
end
end

end OAI
end
