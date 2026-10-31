-- Prove2me | Theorems.Thm_LL_Decomp1535a_norm_S_le
-- name    : LL_Decomp1535a.norm_S_le
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:19:04.637634+00:00
-- url     : https://prove2.me/theorems/a02f69a9-c200-4c78-8132-f90cc73f129f
-- title:
--   Trivial bound for the prime sum
-- statement:
--   For every natural number $N$ and real $\alpha$, $|S_N(\alpha)|\le\theta(N)$.
-- source:
--   Liu and Wang 2002, p. 168, below eq. 6.2

import Mathlib
import Definitions.Def_LL_Decomp1535a_S
import Definitions.Def_LL_Decomp1535a_theta

open MeasureTheory

namespace LL_Decomp1535a
theorem norm_S_le (N : ℕ) (α : ℝ) : ‖S N α‖ ≤ theta N := by sorry
end LL_Decomp1535a
