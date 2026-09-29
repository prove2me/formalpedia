-- Prove2me | Theorems.Thm_Freiman_gap_periodic_unique
-- name    : Freiman.gap_periodic_unique
-- status  : Proved
-- author  : @tp
-- created : 2026-09-09T11:14:43.343933+00:00
-- url     : https://prove2.me/theorems/995758c9-f50c-4387-80bb-cfbe80da5651
-- title:
--   gap periodic unique
-- statement:
--   A nonempty positive-digit period map has at most one fixed point in (0,1); use its continuant determinant and positive denominator.
-- source:
--   Freiman Hall ray report, foundations.tex; continuants and m3_maximum.tex periodic tails

import Definitions.Def_Freiman_gapModel

namespace Freiman

theorem gap_periodic_unique (v : List ℕ+) (hv : v ≠ []) (x y : ℝ) (hx : 0 < x ∧ x < 1) (hy : 0 < y ∧ y < 1) (hfx : prefixEval v x = x) (hfy : prefixEval v y = y) : x = y := by
  sorry

end Freiman
