-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_cond_1_4_iff
-- name    : NagaevLD.FukNagaev.cond_1_4_iff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:23.575715+00:00
-- url     : https://prove2.me/theorems/13ea37c8-13cf-47bf-8089-baa42653c57e
-- title:
--   p. 751 — for B > 0, A > 0: condition (1.4) ⇔ h₁ ≤ max[t/y, h₂], h₁ = αx/e^tB, h₂ = (1/y)log(βxy^{t−1}/A + 1)
-- statement:
--   Let $t\ge2$, $0<\alpha<1$, $\beta=1-\alpha$, $x>0$, $y>0$, and let $B>0$, $A>0$ stand for $B^2(-\infty,Y)$ and $A(t;0,Y)$. Put
--   $$h_1=\frac{\alpha x}{e^tB},\qquad h_2=\frac1y\log\Big(\frac{\beta xy^{t-1}}{A}+1\Big).$$
--   Then condition (1.4), $\max[t,\log(\beta xy^{t-1}/A+1)]\ge\alpha xy/(e^tB)$, holds if and only if
--   $$h_1\le\max[t/y,\,h_2].$$
--
--   $h_1$ and $h_2$ are the minimizers of the two convex parts $f_1(h)=\tfrac12e^tBh^2-\alpha hx$ and $f_2(h)=\frac{e^{hy}-1-hy}{y^t}A-\beta hx$ of the exponent in (1.18). The equivalence translates the case analysis of the proof into the conditions (1.4) and (1.6) of the theorem.
--
--   **Formalization Note** The page writes "the condition $h_1<\max[t/y,h_2]$ is equivalent to (1.4)", right after proving (1.19) "for $h_1\le\max[t/y,h_2]$"; (1.4) is a non-strict inequality, so the strict sign is a misprint and the statement uses $\le$. It is stated for arbitrary positive scalars $A,B$, where $h_1,h_2$ are finite; the case $A=0$ is the separate disjunct of `cond_1_4`.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), pp. 750–751, proof of Theorem 1.3, definition of h₁, h₂ and the sentence after (1.19)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem cond_1_4_iff (t : ℝ) (ht : 2 ≤ t) (α β : ℝ) (hα0 : 0 < α) (hα1 : α < 1)
    (hβ : β = 1 - α) (x : ℝ) (hx : 0 < x) (y : ℝ) (hy0 : 0 < y) (B A : ℝ) (hB : 0 < B)
    (hA : 0 < A) :
    cond_1_4 t α β x y B A ↔
      α * x / (Real.exp t * B) ≤
        max (t / y) (1 / y * Real.log (β * x * y ^ (t - 1) / A + 1)) := by sorry

end NagaevLD.FukNagaev
