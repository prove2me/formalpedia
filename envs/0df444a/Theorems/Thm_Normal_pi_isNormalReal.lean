-- Prove2me | Theorems.Thm_Normal_pi_isNormalReal
-- name    : Normal.pi_isNormalReal
-- status  : Open
-- author  : @Xiang Huang
-- created : 2026-10-07T12:49:40.806709+00:00
-- url     : https://prove2.me/theorems/d0be28c0-73e1-49c5-bafa-403c97ac303f
-- title:
--   π is normal in every base
-- statement:
--   Let $b\ge 2$ be an integer and let $d_b(\pi,n)=\lfloor \pi\, b^{n+1}\rfloor \bmod b$ be the $n$-th base-$b$ digit of $\pi$ after the point. **Conjecture.** $\pi$ is normal in base $b$: for every $k\ge 0$ and every word $w=(w_0,\dots,w_{k-1})$ over $\{0,\dots,b-1\}$,
--   $$\lim_{N\to\infty}\frac{\#\{\,i<N : d_b(\pi,i+j)=w_j \text{ for all } j<k\,\}}{N}=b^{-k}.$$
--   Equivalently, $\pi$ is absolutely normal. This is open for every single base $b$.
-- source:
--   Open problem, implicit in É. Borel, Les probabilités dénombrables et leurs applications arithmétiques, Rend. Circ. Mat. Palermo 27 (1909), 247–271; see D. H. Bailey and R. E. Crandall, On the random character of fundamental constant expansions, Experiment. Math. 10 (2001), 175–190.

import Mathlib
import Definitions.Def_Normal_Core

namespace Normal

theorem pi_isNormalReal (b : ℕ) (hb : 2 ≤ b) : IsNormalReal b Real.pi := by sorry

end Normal
