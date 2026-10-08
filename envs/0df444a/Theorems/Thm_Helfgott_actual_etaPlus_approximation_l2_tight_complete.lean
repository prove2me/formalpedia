-- Prove2me | Theorems.Thm_Helfgott_actual_etaPlus_approximation_l2_tight_complete
-- name    : Helfgott.actual_etaPlus_approximation_l2_tight_complete
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-10-06T06:33:21.792335+00:00
-- url     : https://prove2.me/theorems/2b86179c-6ab4-4d95-8ef9-0e40063593c4
-- title:
--   Tight complete L2 error of the actual Goldbach smoothing
-- statement:
--   The full squared difference of the actual band-limited Goldbach smoothing and its compact reference is integrable and satisfies
--   $$\int_{\mathbb R}|\eta_+(t)-\eta_\circ(t)|^2\,dt\le\frac1{1568000000}.$$
--   This is the already completed smoothing-error estimate extracted from the actual main-convolution proof, so that it can be verified separately. It includes the complete Fourier-cutoff error and all physical tails. No zero-location or prime-accuracy assumption is required.
-- source:
--   Existing complete proof of the tight actual Goldbach main convolution, extracted at its smoothing-error estimate for verifier timeout repair. Helfgott, arXiv:1312.7748v2, section 7.2. Written by Codex.

import Definitions.Def_Helfgott_Smoothings
import Mathlib.MeasureTheory.Integral.Bochner.Basic
open MeasureTheory

namespace Helfgott

theorem actual_etaPlus_approximation_l2_tight_complete :
    Integrable (fun t : ℝ => (etaPlus t-etaCircle t)^2) ∧
    (∫ t : ℝ,(etaPlus t-etaCircle t)^2)≤1/1568000000 := by sorry

end Helfgott
