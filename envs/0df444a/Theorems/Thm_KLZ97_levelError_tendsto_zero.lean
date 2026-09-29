-- Prove2me | Theorems.Thm_KLZ97_levelError_tendsto_zero
-- name    : KLZ97.levelError_tendsto_zero
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T12:35:06.91401+00:00
-- url     : https://prove2.me/theorems/ef60ac24-6577-41ae-a2e3-7e2323244643
-- title:
--   Below threshold the concatenated error tends to $0$
-- statement:
--   Existence of a threshold, in its asymptotic form: if the physical failure parameter $p$ is non-negative and lies below the threshold $1/f$, that is $f p < 1$, then the concatenated failure parameter $E_h$ tends to $0$ as the number $h$ of concatenation levels tends to infinity. This is the sense in which computation of arbitrary accuracy becomes possible below threshold.
-- source:
--   Knill, Laflamme, Zurek, Resilient Quantum Computation: Error Models and Thresholds, arXiv:quant-ph/9702058v1, https://arxiv.org/abs/quant-ph/9702058, Sections I.F and II.C, pp. 6, 8

import Mathlib
import Definitions.Def_KLZ97_model

namespace KLZ97

theorem levelError_tendsto_zero (f p : ℝ) (hf : 0 < f) (hp : 0 ≤ p) (hfp : f * p < 1) :
    Filter.Tendsto (levelError f p) Filter.atTop (nhds 0) := by sorry

end KLZ97
