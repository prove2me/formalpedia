-- Prove2me | Theorems.Thm_KLZ97_levelError_eq_threshold_pow
-- name    : KLZ97.levelError_eq_threshold_pow
-- status  : Proved
-- author  : @Lucas
-- created : 2026-09-21T12:33:49.84142+00:00
-- url     : https://prove2.me/theorems/f6acb5f2-d809-4be6-92b7-3ad51c28adac
-- title:
--   Threshold form of the concatenated error: $E_h = (fp)^{2^h}/f$
-- statement:
--   The level-$h$ failure parameter rewritten so that the threshold is visible: for $f \ne 0$,
--   $$E_h = \frac{(f p)^{2^{h}}}{f}.$$
--   The combination $f p$ is the quantity that must be less than $1$ for concatenation to help, which is the threshold condition $p < 1/f$ of the paper's analysis.
-- source:
--   Knill, Laflamme, Zurek, Resilient Quantum Computation: Error Models and Thresholds, arXiv:quant-ph/9702058v1, https://arxiv.org/abs/quant-ph/9702058, Sections I.F (Concatenation) and II.C (Thresholds for the normalizer group), pp. 6, 8

import Mathlib
import Definitions.Def_KLZ97_model

namespace KLZ97

theorem levelError_eq_threshold_pow (f p : ℝ) (hf : f ≠ 0) (h : ℕ) :
    levelError f p h = (f * p) ^ (2 ^ h) / f := by sorry

end KLZ97
