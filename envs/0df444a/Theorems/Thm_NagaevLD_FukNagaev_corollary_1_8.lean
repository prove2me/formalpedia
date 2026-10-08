-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_corollary_1_8
-- name    : NagaevLD.FukNagaev.corollary_1_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:43.355631+00:00
-- url     : https://prove2.me/theorems/66398bd3-e97f-4b0c-bfba-888862054da2
-- title:
--   Corollary 1.8 (1.24), p. 753 — EX_i = 0, A_t⁺ < ∞, t ≥ 2: P(S_n ≥ x) ≤ (1 + 2/t)^tA_t⁺x^{−t} + exp{−2(t + 2)^{−2}e^{−t}x²/B_n²}
-- statement:
--   Let $X_1,\dots,X_n$ be independent random variables with $\mathbb EX_i=0$ and finite variances $\sigma_i^2$, $B_n^2=\sum_i\sigma_i^2$, and suppose $A_t^+=\sum_i\int_{u\ge0}u^t\,dF_i(u)<\infty$ for some $t\ge2$. Then for every $x>0$,
--   $$P(S_n\ge x)\le c_t^{(1)}A_t^+x^{-t}+\exp\Big\{-\frac{c_t^{(2)}x^2}{B_n^2}\Big\},\qquad c_t^{(1)}=\Big(1+\frac2t\Big)^t,\quad c_t^{(2)}=2(t+2)^{-2}e^{-t}.$$
--
--   This is the form in which the Fuk–Nagaev inequality is usually quoted: the tail of a sum of centred independent variables is at most a polynomial term, governed by the $t$-th moments of the positive parts, plus a Gaussian term governed by the variance. The page obtains it from (1.23) with $y_i=\beta x$ and Chebyshev's inequality.
--
--   **Formalization Note** $B_n^2$ is the sum of Mathlib's `variance (X i) P`, which is $0$ for a variable outside $L^2$; the finiteness of every variance is therefore assumed ($X_i\in L^2$). On the page an infinite $B_n^2$ makes the exponential term $1$ and the bound trivial. If $B_n^2=0$, the exponential term is written as the page's limiting value $0$ ($\exp\{-\infty\}$); Lean's $x/0=0$ would otherwise turn it into $1$. $A_t^+<\infty$ is integrability of $|X_i|^t$ on $\{X_i\ge0\}$. Powers with exponent $t$ are real powers.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), pp. 752–753, Corollary 1.8, (1.24)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem corollary_1_8 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (t : ℝ) (ht : 2 ≤ t)
    (hL2 : ∀ i, MemLp (X i) 2 P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (hAt : ∀ i, IntegrableOn (fun ω => |X i ω| ^ t) {ω | 0 ≤ X i ω} P) :
    P.real {ω | x ≤ S n X ω} ≤
      (1 + 2 / t) ^ t * Atplus P X t * x ^ (-t) +
        (if Bn2 P X = 0 then 0
          else Real.exp (-(2 * (t + 2) ^ (-2 : ℝ) * Real.exp (-t) * x ^ 2 / Bn2 P X))) := by sorry

end NagaevLD.FukNagaev
