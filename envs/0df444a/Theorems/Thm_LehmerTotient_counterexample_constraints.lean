-- Prove2me | Theorems.Thm_LehmerTotient_counterexample_constraints
-- name    : LehmerTotient.counterexample_constraints
-- status  : Open
-- author  : @fangshuming
-- created : 2026-11-26T09:22:39.566805+00:00
-- url     : https://prove2.me/theorems/893e196b-69be-5ada-97e2-01ae59a740cd
-- title:
--   A composite solution is odd, square-free, and has $\omega(n)\ge 7$
-- statement:
--   Let $n>1$ be composite, and suppose that $\varphi(n)$ divides $n-1$. Then $n$ is odd and square-free, and $n$ has at least seven distinct prime factors. This is a known theorem of Lehmer (1932).
-- source:
--   D. H. Lehmer, On Euler's totient function, Bull. Amer. Math. Soc. 38 (1932), 745–751, Theorem 1 (odd and square-free, for n>2) and the conclusion that a composite solution of (1) has at least seven distinct prime factors (summary, p. 751), https://doi.org/10.1090/S0002-9904-1932-05521-5

import Mathlib

namespace LehmerTotient
theorem counterexample_constraints {n : Nat} (hn : 1 < n)
    (hcomp : ¬ Nat.Prime n) (h : Nat.totient n ∣ n - 1) :
    Odd n ∧ Squarefree n ∧ 7 ≤ (Nat.primeFactors n).card := by sorry
end LehmerTotient
