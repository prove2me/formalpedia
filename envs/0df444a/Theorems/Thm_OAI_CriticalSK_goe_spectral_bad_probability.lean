-- Prove2me | Theorems.Thm_OAI_CriticalSK_goe_spectral_bad_probability
-- name    : OAI.CriticalSK.goe_spectral_bad_probability
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-10-25T02:30:10.378759+00:00
-- url     : https://prove2.me/theorems/4b7dea45-2363-44bd-8e49-a3119f900588
-- title:
--   OAI.CriticalSK.goe_spectral_bad_probability: intermediate lemma from OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model
-- statement:
--   An intermediate lemma of the split of OpenAI's proof of `OAI.CriticalSK.covariance_and_linear_tests` and `OAI.CriticalSK.critical_mixing_lower_bounds`, carved from OpenAI's openai/math development for this platform. The statement and its proof are OpenAI's (OpenAI, *Critical slowing down in the Sherrington–Kirkpatrick model*, OpenAI Math Release, September 24, 2026, result family 227, [github.com/openai/math](https://github.com/openai/math), Apache License 2.0); in Lean it is the declaration `OAI.CriticalSK.goe_spectral_bad_probability` of [lean/OAI/MathematicalPhysics/CriticalSK/GOESpectrum.lean](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/GOESpectrum.lean) at commit adc7f12, ported to this platform's Lean and Mathlib.
--
--   **The statement**, as published (namespace `OAI.CriticalSK`, with `open scoped BigOperators Topology NNReal ENNReal`, `open MeasureTheory ProbabilityTheory`, `open scoped ENNReal NNReal`, `open scoped BigOperators InnerProductSpace`, `open Module`, `open scoped BigOperators ENNReal NNReal Real Topology`, `open MeasureTheory ProbabilityTheory Filter`, `open scoped BigOperators NNReal`, `open scoped BigOperators`, `open Matrix Polynomial`, `open scoped BigOperators Topology`, `open Filter`, `open scoped InnerProductSpace`):
--
--   ```lean
--   lemma goe_spectral_bad_probability (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s)
--       (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s)
--       (hsmall : formA n h*(3/8:ℝ)*s^(-5/8:ℝ)+formC n ≤ 1) :
--       (goeLaw (Fin (n+1)) (goeScale n)).real
--         (matrixOrderedEigenvalues ⁻¹' (spectralGood n h s)ᶜ) ≤ 32*Real.exp (-h^2)
--   ```
--
--   **Definitions.** The statement is written with `OAI.CriticalSK.GaussianMatrix`, `OAI.CriticalSK.formA`, `OAI.CriticalSK.formC`, `OAI.CriticalSK.goeLaw`, `OAI.CriticalSK.goeScale`, `OAI.CriticalSK.matrixOrderedEigenvalues`, `OAI.CriticalSK.scaleEnergy` and `OAI.CriticalSK.spectralGood` (definitions bundle `OAIQWCSK000` of this split).
--
--   **Used by.** The proofs of `OAI.CriticalSK.cavity_overlap_tail_zero` and `OAI.CriticalSK.covariance_upper_tight` of this split import it.
-- source:
--   OpenAI, Critical slowing down in the Sherrington–Kirkpatrick model, OpenAI Math Release, September 24, 2026, https://github.com/openai/math (result family 227; paper: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Critical-slowing-down-in-the-Sherrington-Kirkpatrick-model-September-24-2026/paper.pdf; Apache License 2.0); Lean: https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/MathematicalPhysics/CriticalSK/GOESpectrum.lean (declaration OAI.CriticalSK.goe_spectral_bad_probability)

import Mathlib
import Definitions.Def_OAIQWCSK000

section

attribute [-instance] _root_.OAI.CriticalSK.orthogonalGroup_compactSpace _root_.OAI.CriticalSK.orthogonalGroup_measurableSpace
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

lemma goe_spectral_bad_probability (n : ℕ) {h s : ℝ} (hh : 0 ≤ h) (hs : 0 < s)
    (hscale : scaleEnergy (Nat.clog 8 (n+1)) 0 ≤ s)
    (hsmall : formA n h*(3/8:ℝ)*s^(-5/8:ℝ)+formC n ≤ 1) :
    (goeLaw (Fin (n+1)) (goeScale n)).real
      (matrixOrderedEigenvalues ⁻¹' (spectralGood n h s)ᶜ) ≤ 32*Real.exp (-h^2) := by
  sorry

end CriticalSK

end

end OAI
end
