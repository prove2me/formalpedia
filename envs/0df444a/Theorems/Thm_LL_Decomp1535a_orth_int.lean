-- Prove2me | Theorems.Thm_LL_Decomp1535a_orth_int
-- name    : LL_Decomp1535a.orth_int
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:09:30.28898+00:00
-- url     : https://prove2.me/theorems/89978e3b-d4a1-4b53-a3d8-870a9e8900f8
-- title:
--   Orthogonality of exponentials
-- statement:
--   For every integer $k$, $\int_0^1 e^{2\pi i \alpha k}\,d\alpha$ equals $1$ if $k=0$ and $0$ otherwise.
-- source:
--   Liu and Wang 2002, p. 145, behind eq. 3.10

import Mathlib

open MeasureTheory

namespace LL_Decomp1535a
theorem orth_int (k : ℤ) :
    ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0 := by sorry
end LL_Decomp1535a
