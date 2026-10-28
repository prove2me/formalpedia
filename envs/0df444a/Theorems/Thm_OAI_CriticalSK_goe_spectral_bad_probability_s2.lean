-- Prove2me | Theorems.Thm_OAI_CriticalSK_goe_spectral_bad_probability_s2
-- name    : OAI.CriticalSK.goe_spectral_bad_probability_s2
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-28T10:49:57.630092+00:00
-- url     : https://prove2.me/theorems/81f776a3-af0d-4dc6-b9e6-62c6823c2b43
-- title:
--   OAI.CriticalSK.goe_spectral_bad_probability_s2: intermediate lemma from OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227)
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.critical_mixing_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical mixing in the Sherrington-Kirkpatrick model (result family 227)*, OpenAI Math Release, September 25, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.goe_spectral_bad_probability` of [lean/OAI/MathematicalPhysics/CriticalSK/GOESpectrum.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/GOESpectrum.lean) at commit adc7f12, ported to Lean 4.33.1 and Mathlib 0df444a.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open scoped BigOperators InnerProductSpace`, `open Module`, `open scoped BigOperators ENNReal NNReal Real Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open Matrix Polynomial`, `open scoped BigOperators Topology`, `open Filter`, `open scoped InnerProductSpace`):
--
--   ```lean
--   lemma goe_spectral_bad_probability_s2 (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s)
--       (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s)
--       (hsmall : formA n h*(3/8:ℝ)*s^(-5/8:ℝ)+formC n ≤ 1) :
--       (goeLaw (Fin (n+1)) (goeScale n)).real
--         (matrixOrderedEigenvalues ⁻¹' (spectralGood n h s)ᶜ) ≤ 32*Real.exp (-h^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.GaussianMatrix`, `OAI.CriticalSK.formA`, `OAI.CriticalSK.formC`, `OAI.CriticalSK.goeLaw`, `OAI.CriticalSK.goeScale`, `OAI.CriticalSK.matrixOrderedEigenvalues`, `OAI.CriticalSK.scaleEnergy` and `OAI.CriticalSK.spectralGood` (definitions bundle `OAIQ074C000` of this split).
--
--   **Used by.** The proof of `OAI.CriticalSK.natural_smallBallObstruction_probability_s2` of this split imports it.
-- source:
--   OpenAI, Critical mixing in the Sherrington-Kirkpatrick model (result family 227), OpenAI Math Release, September 25, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-mixing-in-the-Sherrington-Kirkpatrick-model-September-25-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/GOESpectrum.lean (declaration OAI.CriticalSK.goe_spectral_bad_probability)

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

open scoped InnerProductSpace

lemma goe_spectral_bad_probability_s2 (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s)
    (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s)
    (hsmall : formA n h*(3/8:ℝ)*s^(-5/8:ℝ)+formC n ≤ 1) :
    (goeLaw (Fin (n+1)) (goeScale n)).real
      (matrixOrderedEigenvalues ⁻¹' (spectralGood n h s)ᶜ) ≤ 32*Real.exp (-h^2) := by
  sorry

end CriticalSK

end

end OAI
end
