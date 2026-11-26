-- Prove2me | Theorems.Thm_LogLogJam_Supplement_phase_count_reconstruction
-- name    : LogLogJam.Supplement.phase_count_reconstruction
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-26T09:18:20.479883+00:00
-- url     : https://prove2.me/theorems/448e4d1a-350e-4fbe-b109-4411928767bd
-- title:
--   Joint trace-distance guarantee from phase and photon-count data
-- statement:
--   Consider any measure on transcripts and one-mode density operators consisting of the true state and two transcript-dependent estimates. The first estimate has the estimated angle and true squeezing. Suppose its trace-distance error exceeds $a\geq0$ on mass at most $d_1$. Suppose a nonnegative count-mean estimate deviates from $\sinh^2r$ by more than $\eta\cosh(r)\sinh(r)$ on mass at most $d_2$, where $r\geq0$ and $0\leq\eta\leq1/4$. If the distance between the two estimates obeys the equal-angle formula (179) with reconstructed squeezing $\operatorname{arsinh}\sqrt\mu$, the final trace error exceeds $a+4\eta$ on mass at most $d_1+d_2$.
-- source:
--   https://arxiv.org/html/2607.12983v1#S8.SS3 — §8.3.4, Eqs. (177)–(179)

import Definitions.Def_BosonicLearn_FockPOVM
import Definitions.Def_BosonicLearn_traceDist
import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Claimed50_P47

open MeasureTheory BosonicLearn
open QAlgorithms.Papers.Independent.Dependency50.P33 (State)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open scoped ENNReal

namespace LogLogJam.Supplement

theorem phase_count_reconstruction
    {X : Type} [MeasurableSpace X] (ν : Measure X)
    (ρ : State (Occupation (Fin 1))) (mid est : X → State (Occupation (Fin 1)))
    (μ : X → ℝ) {r a η : ℝ} {d₁ d₂ : ℝ≥0∞}
    (hr : 0 ≤ r) (ha : 0 ≤ a) (hη : 0 ≤ η) (hsmall : η ≤ 1 / 4) (hμ : ∀ x, 0 ≤ μ x)
    (phase : ν {x | ENNReal.ofReal a < traceDist ρ.coefficients (mid x).coefficients} ≤ d₁)
    (count : ν {x | η * Real.cosh r * Real.sinh r < |μ x - Real.sinh r ^ 2|} ≤ d₂)
    (sameAngle : ∀ x, traceDist (mid x).coefficients (est x).coefficients =
      ENNReal.ofReal (Real.sqrt (1 - 1 / Real.cosh (Real.arsinh (Real.sqrt (μ x)) - r)))) :
    ν {x | ENNReal.ofReal (a + 4 * η) < traceDist ρ.coefficients (est x).coefficients} ≤ d₁ + d₂ := by sorry

end LogLogJam.Supplement
