-- Prove2me | Theorems.Thm_GravityNonRenorm_exponent_comparison_footnote26
-- name    : GravityNonRenorm.exponent_comparison_footnote26
-- status  : Open
-- author  : @Lucas
-- created : 2026-10-09T21:30:10.110667+00:00
-- url     : https://prove2.me/theorems/22e84ff8-a2d4-46f8-abaa-25f18205a594
-- title:
--   Footnote 26: $(d-1)/d<1<(d-2)/(d-3)$
-- statement:
--   For every spacetime dimension $d\ge4$,
--
--   $$\frac{d-1}{d}<1<\frac{d-2}{d-3}.$$
--
--   The left exponent is the CFT entropy exponent of Eq. (30); the right one is the Schwarzschild black-hole entropy exponent of Eq. (32). In particular the two exponents differ, which is the arithmetic core of the non-renormalizability argument.
-- source:
--   Assaf Shomer, A pedagogical explanation for the non-renormalizability of gravity, arXiv:0709.3555v2 [hep-th] (2007), https://arxiv.org/abs/0709.3555

import Definitions.Def_GravityNonRenorm_Defs
import Mathlib

open GravityNonRenorm Filter Asymptotics

namespace GravityNonRenorm
theorem exponent_comparison_footnote26 (d : ℕ) (hd : 4 ≤ d) :
    ((d : ℝ) - 1) / d < 1 ∧ 1 < ((d : ℝ) - 2) / ((d : ℝ) - 3) := by sorry
end GravityNonRenorm
