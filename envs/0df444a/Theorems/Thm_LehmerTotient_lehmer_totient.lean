-- Prove2me | Theorems.Thm_LehmerTotient_lehmer_totient
-- name    : LehmerTotient.lehmer_totient
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:43.7398+00:00
-- url     : https://prove2.me/theorems/7809317f-ab1e-5718-860a-6799540c6bb6
-- title:
--   If $\varphi(n)\mid n-1$ and $n>1$, then $n$ is prime
-- statement:
--   Let $n>1$ be a natural number such that $\varphi(n)$ divides $n-1$. Then $n$ is prime. Equivalently, there is no composite natural number $n$ for which $\varphi(n)$ divides $n-1$. This is Lehmer's totient problem, which remains open. The hypothesis $n>1$ is essential in Lean: the unguarded implication fails at $n=0$ (where truncated subtraction gives $0\mid 0$) and at $n=1$ (where $\varphi(1)=1$ divides $0$).
-- source:
--   D. H. Lehmer, On Euler's totient function, Bull. Amer. Math. Soc. 38 (1932), 745–751, equation (1) and the question of composite solutions, https://doi.org/10.1090/S0002-9904-1932-05521-5

import Mathlib

namespace LehmerTotient
theorem lehmer_totient {n : Nat} (hn : 1 < n)
    (h : Nat.totient n ∣ n - 1) : Nat.Prime n := by sorry
end LehmerTotient
