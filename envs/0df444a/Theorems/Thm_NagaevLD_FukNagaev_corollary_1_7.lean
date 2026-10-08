-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_corollary_1_7
-- name    : NagaevLD.FukNagaev.corollary_1_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:33:35.480077+00:00
-- url     : https://prove2.me/theorems/326d0162-fd6d-4745-85cf-1bf4ef9a5d8c
-- title:
--   Corollary 1.7 (1.23), p. 752 — EX_i = 0, β = t/(t+2): P(S_n ≥ x) ≤ ΣP(X_i > y_i) + exp{−α²x²/2e^tB²(−∞, Y)} + (A(t; 0, Y)/βxy^{t−1})^{βx/y}
-- statement:
--   Let $X_1,\dots,X_n$ be independent random variables with $\mathbb EX_i=0$, $x>0$, $y_1,\dots,y_n>0$, $y\ge\max_iy_i$, and $B^2(-\infty,Y)<\infty$. Suppose $t\ge2$, $\beta=t/(t+2)$ and $\alpha=1-\beta$. Then
--   $$P(S_n\ge x)\le\sum_{i=1}^nP(X_i>y_i)+\exp\Big\{-\frac{\alpha^2x^2}{2e^tB^2(-\infty,Y)}\Big\}+\Big(\frac{A(t;0,Y)}{\beta xy^{t-1}}\Big)^{\beta x/y}.$$
--
--   It follows from Theorem 1.3 with this choice of $\beta$, for which $\beta=t\alpha/2$. It is the single-formula form of the Fuk–Nagaev inequality: a Gaussian term in the truncated variance plus a polynomial term in the truncated $t$-th moment.
--
--   **Formalization Note** $\mathbb EX_i=0$ is stated with integrability of $X_i$. $B^2(-\infty,Y)<\infty$ is assumed summand by summand, as in Theorem 1.3. The last term is a real power; for $A(t;0,Y)=0$ it is $0$, the page's value. If $B^2(-\infty,Y)=0$, the exponential term is written as the page's limiting value $0$ ($\exp\{-\infty\}$); Lean's $x/0=0$ would otherwise turn it into $1$ and weaken the bound.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 752, Corollary 1.7, (1.23)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem corollary_1_7 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (hint : ∀ i, Integrable (X i) P) (hmean : ∀ i, ∫ ω, X i ω ∂P = 0)
    (α β : ℝ) (hβ : β = t / (t + 2)) (hα : α = 1 - β)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P) :
    P.real {ω | x ≤ S n X ω} ≤
      ∑ i, P.real {ω | yv i < X i ω} +
        (if B2Y P X yv = 0 then 0
          else Real.exp (-(α ^ 2 * x ^ 2 / (2 * Real.exp t * B2Y P X yv)))) +
        (AY P X yv t / (β * x * y ^ (t - 1))) ^ (β * x / y) := by sorry

end NagaevLD.FukNagaev
