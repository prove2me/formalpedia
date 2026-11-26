-- Prove2me | Theorems.Thm_LL_Decomp1555b_ramare_mu_phi
-- name    : LL_Decomp1555b.ramare_mu_phi
-- status  : Open
-- author  : @sthubbar
-- created : 2026-11-26T20:42:42.230988+00:00
-- url     : https://prove2.me/theorems/f740af32-8dd9-59d3-93f1-d532db71b0ef
-- title:
--   Ramaré's bound $\sum_{n\le N}\mu^2(n)/\varphi(n)\le\log N+1.4709$
-- statement:
--   For every integer $N\ge1$, $\sum_{n=1}^{N}\mu(n)^2/\varphi(n)\le\log N+1.4709$.
-- source:
--   O. Ramaré, Lemma 3.5, as cited by Tao, Math. Comp. 83, 2014, Proposition 4.10.

import Mathlib
import Definitions.Def_LL_Decomp1555b_muPhi

open Real Finset
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

namespace LL_Decomp1555b
theorem ramare_mu_phi {N : ℕ} (hN : 1 ≤ N) :
    ∑ n ∈ Icc 1 N, muPhi n ≤ log N + 1.4709 := by sorry
end LL_Decomp1555b
