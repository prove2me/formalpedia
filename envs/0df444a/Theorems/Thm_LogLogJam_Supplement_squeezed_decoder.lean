-- Prove2me | Theorems.Thm_LogLogJam_Supplement_squeezed_decoder
-- name    : LogLogJam.Supplement.squeezed_decoder
-- status  : Open
-- author  : @Senrui Chen
-- created : 2026-11-26T09:27:21.457573+00:00
-- url     : https://prove2.me/theorems/ef18678f-c3e9-52c7-884a-7c9c3d4787c5
-- title:
--   Physical squeezed-state coordinate decoder and its trace distances
-- statement:
--   There exists a measurable physical-state decoder $D(r,\theta)$ covering every centered pure one-mode Gaussian state. For $r\ge0$ its output has Siegel parameter $\tanh(r)e^{2i\theta}$. At equal squeezing the trace distance is the determinant formula of Task 5.1 with $\lambda=e^{2r}$. At equal angle and squeezings $r,s\ge0$ the distance is $\sqrt{1-1/\cosh(s-r)}$.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — §§4.4 and 8.3.4, Eqs. (144), (177)–(179).

import Mathlib
import Definitions.Def_LogLogJam_Supplement_phaseCountReadouts
import Definitions.Def_BosonicLearn_traceDist

open MeasureTheory
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)

namespace LogLogJam.Supplement

theorem squeezed_decoder :
    ∃ D : ℝ × ℝ → State (Occupation (Fin 1)), Measurable D ∧
    (∀ r θ : ℝ, 0 ≤ r → squeezedAt (D (r, θ)) r θ ∧ IsPureCentGauss (D (r, θ))) ∧
    (∀ ρ : State (Occupation (Fin 1)), IsPureCentGauss ρ → ∃ r θ : ℝ, 0 ≤ r ∧ D (r, θ) = ρ) ∧
    (∀ r θ φ : ℝ, 0 ≤ r → BosonicLearn.traceDist (D (r, θ)).coefficients (D (r, φ)).coefficients =
      ENNReal.ofReal (LogLogJam.trDist (Real.exp (2 * r)) θ φ)) ∧
    (∀ r s θ : ℝ, 0 ≤ r → 0 ≤ s →
      BosonicLearn.traceDist (D (r, θ)).coefficients (D (s, θ)).coefficients =
        ENNReal.ofReal (Real.sqrt (1 - 1 / Real.cosh (s - r)))) := by sorry

end LogLogJam.Supplement
