-- Prove2me | Theorems.Thm_LL_JSConstants_euler_lt_057722
-- name    : LL_JSConstants.euler_lt_057722
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-23T17:43:18.687521+00:00
-- url     : https://prove2.me/theorems/ad10640e-d7e2-4fec-a963-2c846eaf9a98
-- title:
--   The Euler-Mascheroni constant is below $0.57722$
-- statement:
--   The Euler-Mascheroni constant $\gamma=\lim_{n\to\infty}\bigl(\sum_{k=1}^n \frac1k-\log n\bigr)$ satisfies $\gamma<0.57722$.
-- source:
--   Johnston and Starichkova, Some explicit results on the sum of a prime and an almost prime, arXiv:2208.01229v3, page 3, factor $e^{-\gamma}$ in $U_N$.

import Mathlib

namespace LL_JSConstants
theorem euler_lt_057722 : Real.eulerMascheroniConstant < (0.57722 : ℝ) := by sorry
end LL_JSConstants
