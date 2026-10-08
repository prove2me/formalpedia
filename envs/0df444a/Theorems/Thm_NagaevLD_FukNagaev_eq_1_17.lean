-- Prove2me | Theorems.Thm_NagaevLD_FukNagaev_eq_1_17
-- name    : NagaevLD.FukNagaev.eq_1_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:32:29.832828+00:00
-- url     : https://prove2.me/theorems/f5e1ef18-b90f-429c-966e-90af9617fae2
-- title:
--   (1.17), p. 750 — P(S̃_n ≥ x) ≤ exp{h(μ(−∞, Y) − x) + ½e^tB²(−∞, Y)h²} for 0 < h ≤ t/y
-- statement:
--   Let $X_1,\dots,X_n$ be independent random variables, $x>0$, $y_1,\dots,y_n>0$, $y\ge\max_iy_i$, $t\ge2$, and suppose $B^2(-\infty,Y)=\sum_i\int_{u\le y_i}u^2\,dF_i(u)<\infty$. With $\tilde S_n$ the sum of the truncated summands and $\mu(-\infty,Y)=\sum_i\int_{u\le y_i}u\,dF_i(u)$, for $0<h\le t/y$,
--   $$P(\tilde S_n\ge x)\le\exp\Big\{h\big(\mu(-\infty,Y)-x\big)+\tfrac12e^tB^2(-\infty,Y)h^2\Big\}.$$
--
--   It is (1.9) combined with Lemma 1.4 (1.10) applied to every factor $\mathbb Ee^{h\tilde X_i}$. Choosing $h$ in it gives the Gaussian-type bounds $P_6$ and $P_5$.
--
--   **Formalization Note** The finiteness of $B^2(-\infty,Y)$ is assumed as integrability of $X_i^2$ on $\{X_i\le y_i\}$ for every $i$; on the page an infinite $B^2(-\infty,Y)$ makes the bound trivial, while Lean would replace it by $0$. The bound $y>0$ is stated explicitly; it follows from $y\ge y_i>0$ whenever $n\ge1$.
-- source:
--   Nagaev, Large deviations of sums of independent random variables, Ann. Probab. 7 (1979), p. 750, proof of Theorem 1.3, (1.17)

import Mathlib
import Definitions.Def_NagaevLD_FukNagaev_Setting

namespace NagaevLD.FukNagaev

open MeasureTheory ProbabilityTheory

theorem eq_1_17 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n : ℕ} (X : Fin n → Ω → ℝ) (hmeas : ∀ i, Measurable (X i)) (hindep : iIndepFun X P)
    (x : ℝ) (hx : 0 < x) (yv : Fin n → ℝ) (hyv : ∀ i, 0 < yv i)
    (y : ℝ) (hy0 : 0 < y) (hyy : ∀ i, yv i ≤ y)
    (t : ℝ) (ht : 2 ≤ t)
    (hL2 : ∀ i, IntegrableOn (fun ω => X i ω ^ 2) {ω | X i ω ≤ yv i} P)
    (h : ℝ) (hh : 0 < h) (hht : h ≤ t / y) :
    P.real {ω | x ≤ St X yv ω} ≤
      Real.exp (h * (muY P X yv - x) + 1 / 2 * Real.exp t * B2Y P X yv * h ^ 2) := by sorry

end NagaevLD.FukNagaev
