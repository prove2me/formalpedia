-- Prove2me | Theorems.Thm_LL_Decomp1535a_circle_identity_of_orth
-- name    : LL_Decomp1535a.circle_identity_of_orth
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:10:16.176783+00:00
-- url     : https://prove2.me/theorems/b39c5cc3-96cd-409b-ada5-bbf028663dbb
-- title:
--   Circle identity for the weighted count
-- statement:
--   Assume that for every integer $k$, $\int_0^1 e^{2\pi i \alpha k}\,d\alpha$ equals $1$ if $k=0$ and $0$ otherwise. Then for every natural number $N$, $R_3(N)$, viewed as a complex number, equals $\int_0^1 F_N(\alpha)\,d\alpha$.
-- source:
--   Liu and Wang 2002, p. 145, eq. 3.10

import Mathlib
import Definitions.Def_LL_Decomp1535a_R3
import Definitions.Def_LL_Decomp1535a_S
import Definitions.Def_LL_Decomp1535a_F

open MeasureTheory

namespace LL_Decomp1535a
theorem circle_identity_of_orth
    (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    (R3 N : ℂ) = ∫ α in (0 : ℝ)..1, F N α := by sorry
end LL_Decomp1535a
