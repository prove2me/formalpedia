-- Prove2me | Theorems.Thm_OAI_CriticalSK_triSample_eigenvalue_good_s2
-- name    : OAI.CriticalSK.triSample_eigenvalue_good_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:51:59.71+00:00
-- url     : https://prove2.me/theorems/01e6fe1c-d2d1-455b-a3e0-cb43eae5d128
-- title:
--   OAI.CriticalSK.triSample_eigenvalue_good_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.triSample_eigenvalue_good` of [lean/OAI/MathematicalPhysics/CriticalSK/Resolvent.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/Resolvent.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open scoped BigOperators InnerProductSpace`, `open Module`, `open scoped BigOperators ENNReal NNReal Real Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open Matrix Polynomial`, `open scoped BigOperators Topology`, `open Filter`, `open MeasureTheory Set`, `open MeasureTheory Set`):
--
--   ```lean
--   lemma triSample_eigenvalue_good_s2 (n : ℕ) {ω : TriSample n} {h s : ℝ}
--       (hh : 0 ≤ h) (hs : 0 < s) (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s)
--       (hsmall : formA n h*(3/8:ℝ)*s^(-5/8:ℝ)+formC n ≤ 1)
--       (hω : ω ∉ triBad n h) (i : Fin (n+1)) :
--       |sampleEigenvalues n ω i-(2-orderedJacobiGaps n i)| ≤
--         edgeError (formA n h) (formB n) (formC n) s (orderedJacobiGaps n i)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.TriSample`, `OAI.CriticalSK.edgeError`, `OAI.CriticalSK.formA`, `OAI.CriticalSK.formB`, `OAI.CriticalSK.formC`, `OAI.CriticalSK.orderedJacobiGaps`, `OAI.CriticalSK.sampleEigenvalues`, `OAI.CriticalSK.scaleEnergy` and `OAI.CriticalSK.triBad` (definitions bundle `OAIQ074C000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalSK.goe_spectral_bad_probability_s2` of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/Resolvent.lean (declaration OAI.CriticalSK.triSample_eigenvalue_good)

import Mathlib
import Definitions.Def_OAIQ074C000

section

attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace _root_.OAI.SKGap.ComplexMatrix.frobeniusInnerProduct
set_option linter.all false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace OAI

noncomputable section

open scoped BigOperators Topology NNReal ENNReal

open MeasureTheory ProbabilityTheory

open scoped ENNReal NNReal

open scoped BigOperators InnerProductSpace

open Module

open scoped BigOperators ENNReal NNReal Real Topology

open MeasureTheory ProbabilityTheory Filter

open scoped BigOperators NNReal

open scoped BigOperators

open Matrix Polynomial

open scoped BigOperators Topology

open Filter

namespace CriticalSK

open MeasureTheory Set

open MeasureTheory Set

lemma triSample_eigenvalue_good_s2 (n : ℕ) {ω : TriSample n} {h s : ℝ}
    (hh : 0 ≤ h) (hs : 0 < s) (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s)
    (hsmall : formA n h*(3/8:ℝ)*s^(-5/8:ℝ)+formC n ≤ 1)
    (hω : ω ∉ triBad n h) (i : Fin (n+1)) :
    |sampleEigenvalues n ω i-(2-orderedJacobiGaps n i)| ≤
      edgeError (formA n h) (formB n) (formC n) s (orderedJacobiGaps n i) := by
  sorry

end CriticalSK

end

end OAI
end
