-- Prove2me | Theorems.Thm_LL_Decomp1543c_lemma62_S1
-- name    : LL_Decomp1543c.lemma62_S1
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T17:33:32.862755+00:00
-- url     : https://prove2.me/theorems/37d979a7-467b-4adb-8ede-442842eb4de9
-- title:
--   Bound for $S_1$ (Lemma 6.2)
-- statement:
--   For every real $c$, $\alpha$ and natural $N$ with $\log N\ge3100$, $|S_{\Lambda_1(U,\cdot)}(c,N,\alpha)|\le1.02\,U$, where $U=N^{2/5}(\log N)^{-4/5}$ and $\Lambda_1(U,n)$ is $\Lambda(n)$ for $n\le U$ and $0$ otherwise. No sign condition on $c$ is assumed.
-- source:
--   M. C. Liu and T. Z. Wang, On the Vinogradov bound in the three primes Goldbach conjecture, Acta Arith. 105, 2002, p. 169, Lemma 6.2. https://doi.org/10.4064/aa105-2-3

import Mathlib
import Definitions.Def_LL_Decomp1543c_e
import Definitions.Def_LL_Decomp1543c_rangeN
import Definitions.Def_LL_Decomp1543c_Ssum
import Definitions.Def_LL_Decomp1543c_lam1
import Definitions.Def_LL_Decomp1543c_Uf

open Real Finset ArithmeticFunction

namespace LL_Decomp1543c
theorem lemma62_S1 (c : ℝ) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) :
    ‖Ssum (lam1 (Uf N)) c N α‖ ≤ 1.02 * Uf N := by sorry
end LL_Decomp1543c
