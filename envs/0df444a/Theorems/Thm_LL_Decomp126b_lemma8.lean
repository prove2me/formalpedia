-- Prove2me | Theorems.Thm_LL_Decomp126b_lemma8
-- name    : LL_Decomp126b.lemma8
-- status  : Open
-- author  : @sthubbar
-- created : 2026-10-29T15:52:25.63974+00:00
-- url     : https://prove2.me/theorems/18289e61-e64f-44ba-bb04-68610a0908c7
-- title:
--   Lemma 8: primality criterion with a cubic factored part
-- statement:
--   The proposition lemma8_stmt holds: for natural numbers $N,R,F,s,r$ with $N\ge2$, $F\ge2$ even, $\gcd(R,F)=1$, $N$ odd, $N=RF+1$, $R=2Fs+r$, $0\le r<2F$ and $N<2F^3$, if some $a\in\mathbb Z$ satisfies $a^{N-1}\equiv1\pmod N$ and $\gcd(a^{(N-1)/p}-1,N)=1$ for every prime $p\mid F$, then $N$ is prime if and only if $s=0$ or $r^2-8s$ is not a perfect square in $\mathbb Z$. In the lab this assembly is conditional on the open Pocklington leaf.
-- source:
--   O. Ramaré and Y. Saouter, Short effective intervals containing primes, Journal of Number Theory 98 (2003), 10 to 33. ; Lemma 8 and its proof, p. 27

import Mathlib
import Definitions.Def_LL_Decomp126b_lemma8_stmt

namespace LL_Decomp126b
theorem lemma8 : lemma8_stmt := by sorry
end LL_Decomp126b
