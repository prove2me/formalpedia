-- Prove2me | Theorems.Thm_LL_Decomp1535a_parseval_of_orth
-- name    : LL_Decomp1535a.parseval_of_orth
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-30T14:10:38.715691+00:00
-- url     : https://prove2.me/theorems/b1955120-b732-4c94-a2ca-ee1dd34a4415
-- title:
--   Parseval identity for the prime sum
-- statement:
--   Assume that for every integer $k$, $\int_0^1 e^{2\pi i \alpha k}\,d\alpha$ equals $1$ if $k=0$ and $0$ otherwise. Then for every natural number $N$, $\int_0^1 |S_N(\alpha)|^2\,d\alpha=\sum_{p\le N,\ p\text{ prime}} (\log p)^2$.
-- source:
--   Liu and Wang 2002, p. 174, proof of Theorem 1

import Mathlib
import Definitions.Def_LL_Decomp1535a_S

open MeasureTheory

namespace LL_Decomp1535a
theorem parseval_of_orth
    (horth : ∀ k : ℤ, ∫ α in (0 : ℝ)..1, Complex.exp (2 * Real.pi * Complex.I * α * k) =
      if k = 0 then 1 else 0) (N : ℕ) :
    ∫ α in (0 : ℝ)..1, ‖S N α‖ ^ 2 =
      ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p ^ 2 := by sorry
end LL_Decomp1535a
