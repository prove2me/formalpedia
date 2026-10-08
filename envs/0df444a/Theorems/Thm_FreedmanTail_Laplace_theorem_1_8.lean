-- Prove2me | Theorems.Thm_FreedmanTail_Laplace_theorem_1_8
-- name    : FreedmanTail.Laplace.theorem_1_8
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:22:47.868178+00:00
-- url     : https://prove2.me/theorems/b624fb35-b5bd-4df2-a364-2f788fa5c1c2
-- title:
--   (1.8) Theorem, p. 102 — E{exp[−f(λ)W_a]} ≥ exp[−λ(a + 1)] for a > 0
-- statement:
--   Let $(\Omega, \mathcal F, P)$ be a probability space with filtration $\mathcal F_0 \subset \mathcal F_1 \subset \cdots$, and let $X_1, X_2, \dots$ be random variables, $X_n$ being $\mathcal F_n$-measurable, with
--   $$
--   |X_n| \le 1 \quad\text{and}\quad E\{X_n \mid \mathcal F_{n-1}\} = 0 \qquad (n \ge 1).
--   $$
--   Let $V_n = \operatorname{Var}\{X_n \mid \mathcal F_{n-1}\}$, $S_n = X_1 + \cdots + X_n$, $T_n = V_1 + \cdots + V_n$, and $f(\lambda) = e^{-\lambda} - 1 + \lambda$. For $a > 0$ let $\tau_a$ be the least $n$ with $S_n \ge a$ ($\tau_a = \infty$ if there is none) and $W_a = T_{\tau_a} \in [0, \infty]$, the conditional variance used to cross the level $a$. Then for every $\lambda > 0$ and $a > 0$,
--   $$
--   E\{\exp[-f(\lambda) W_a]\} \ge \exp[-\lambda(a+1)] ,
--   $$
--   where $\exp[-f(\lambda) W_a] = 0$ on the event $\{W_a = \infty\}$.
--
--   The theorem prevents $W_a$ from being too large: by Chebyshev's inequality it gives $P\{W_a \ge b\} < 5(a+1)/b^{1/2}$ (Corollary (1.9)), it implies Lévy's theorem that $\sup_n S_n = \infty$ almost surely on $\{\sum V_i = \infty\}$, and it is the input of the lower half of the law of the iterated logarithm in Freedman's paper.
--
--   **Formalization Note** Condition (1.1) is assumed almost surely; with $\mathcal F_n$-measurability it makes each $X_n$ square-integrable, so $V_n$ is a genuine conditional variance. $W_a$ takes values in $[0, \infty]$ and the integrand is $e^{-f(\lambda) W_a}$ on $\{W_a < \infty\}$ and $0$ on $\{W_a = \infty\}$; it lies in $[0, 1]$, so the Bochner integral is genuine.
-- source:
--   Freedman, On Tail Probabilities for Martingales, Ann. Probab. 3 (1975), p. 102 (PDF p. 3), (1.8) Theorem; proof (4.2), p. 108 (PDF p. 9)

import Mathlib
import Definitions.Def_FreedmanTail_Laplace_Exponents
import Definitions.Def_FreedmanTail_Bernstein_PartialSums
import Definitions.Def_FreedmanTail_Laplace_CrossingTime

open MeasureTheory ProbabilityTheory

namespace FreedmanTail.Laplace

/-- Freedman (1975), (1.8) Theorem, p. 102 (proved in (4.2), p. 108): under condition (1.1)
(`|X_n| ≤ 1` and `E{X_n | ℱ_{n−1}} = 0` for `n ≥ 1`), for `λ > 0` and `a > 0`,
`E{exp[−f(λ)W_a]} ≥ exp[−λ(a + 1)]`, where `W_a = T_{τ_a} ∈ [0, ∞]` is the conditional variance
accumulated up to the first crossing of level `a`, and `exp[−f(λ)·∞] = 0`. -/
theorem theorem_1_8 {Ω : Type*} {m : MeasurableSpace Ω} (P : Measure Ω)
    [IsProbabilityMeasure P] (ℱ : Filtration ℕ m) (X : ℕ → Ω → ℝ)
    (hX_meas : ∀ n, 1 ≤ n → StronglyMeasurable[ℱ n] (X n))
    (hX_bdd : ∀ n, 1 ≤ n → ∀ᵐ ω ∂P, |X n ω| ≤ 1)
    (hX_mart : ∀ n, 1 ≤ n → P[X n | ℱ (n - 1)] =ᵐ[P] 0)
    (lam : ℝ) (hlam : 0 < lam) (a : ℝ) (ha : 0 < a) :
    Real.exp (-(lam * (a + 1))) ≤ ∫ ω, expNegMul (f lam) (W a ℱ X P ω) ∂P := by sorry

end FreedmanTail.Laplace
