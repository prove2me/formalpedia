-- Prove2me | Theorems.Thm_OptimalSGD_LowerBound_theorem_4
-- name    : OptimalSGD.LowerBound.theorem_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:17.330257+00:00
-- url     : https://prove2.me/theorems/02d4528a-2794-4774-9013-aff81cf73604
-- title:
--   Theorem 4 — averaged SGD on a non-smooth problem with interior optimum: E[F(w̄_T) − F(w*)] ≥ (3c/16T) Σ_{t=T₀+2}^{T} 1/t − T₀/T
-- statement:
--   Consider Example B: the domain $W=[-1,1]^d$ and the $1$-strongly convex, non-smooth objective
--   $$F(w)=\tfrac12\|w\|^2+\begin{cases}w_1&w_1\ge0\\-7w_1&w_1<0,\end{cases}$$
--   where $w_1$ is the first coordinate of $w$; its global minimum is $w^*=0$, an interior point of $W$. At the query point $w_t$ the stochastic gradient oracle returns
--   $$\hat g_t=w_t+\begin{cases}(Z_t,0,\dots,0)&w_{t,1}\ge0\\(-7,0,\dots,0)&w_{t,1}<0,\end{cases}$$
--   with $Z_1,Z_2,\dots$ independent and uniformly distributed on $[-1,3]$; its mean is a subgradient of $F$ at $w_t$.
--
--   Let $c>0$ and run projected SGD $w_{t+1}=\Pi_W(w_t-\eta_t\hat g_t)$ with $\eta_t=c/t$ from any starting point $w_1\in W$ with $w_{1,1}\ge0$. Let $\bar w_T=\frac1T(w_1+\dots+w_T)$ and $T_0=\max\{2,6c+1\}$. Then for every integer $T\ge T_0+2$,
--   $$\mathbb E\big[F(\bar w_T)-F(w^*)\big]\ \ge\ \frac{3c}{16T}\sum_{t=T_0+2}^{T}\frac1t\ -\ \frac{T_0}{T},$$
--   where the sum runs over the integers $t$ with $T_0+2\le t\le T$.
--
--   For fixed $c$ the right-hand side is of order $\log(T)/T$; it is positive only once $\log(T/T_0)$ exceeds roughly $16(6c+1)/(3c)$. The theorem shows that the $\log(T)/T$ rate of SGD with averaging on strongly convex problems cannot be improved in general, even when the optimum lies in the interior of the domain.
--
--   **Formalization Note** The expectation is the Bochner integral over the law $\mathrm{Unif}[-1,3]^{\otimes T}$ of $(Z_1,\dots,Z_T)$; the statement also asserts that $F(\bar w_T)-F(0)$ is integrable. $T_0$ is real; $T$ is a natural number with $T\ge T_0+2$, and the sum is over `Finset.Icc (⌈T₀⌉₊ + 2) T`. $d\ge1$ and $c>0$; $\mathbb R^d$ stands for the paper's Euclidean space.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 5, Theorem 4 (example on p. 5; proof App. B.5, pp. 16–17)

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_UnderstandingML_Linear
import Definitions.Def_OptimalSGD_LowerBound_Model

namespace OptimalSGD.LowerBound

open MeasureTheory UnderstandingML

/-- **Theorem 4** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7, p. 5). On Example B
(`W = [−1, 1]^d`, `F(w) = ½‖w‖² + (w₁ if w₁ ≥ 0, −7w₁ if w₁ < 0)`, oracle
`ĝ = w + ((Z, 0, …, 0) if w₁ ≥ 0, (−7, 0, …, 0) if w₁ < 0)`, `Z ∼ Unif[−1, 3]` i.i.d.), SGD
initialized at any `w₁ ∈ W` with `w₁,₁ ≥ 0` and run with `η_t = c/t` satisfies, for every
`T ≥ T₀ + 2` with `T₀ = max{2, 6c + 1}`,
`E[F(w̄_T) − F(w*)] ≥ (3c/(16T)) ∑_{t=T₀+2}^{T} 1/t − T₀/T`, where `w* = 0`.
The sum ranges over the integers `t` with `T₀ + 2 ≤ t ≤ T`. -/
theorem theorem_4 (d : ℕ) [NeZero d] (c : ℝ) (hc : 0 < c) (w₁ : Vec d)
    (hw₁ : w₁ ∈ box (-1) 1) (hw₁₁ : 0 ≤ w₁ 0) (T : ℕ)
    (hT : max 2 (6 * c + 1) + 2 ≤ (T : ℝ)) :
    Integrable (fun Z : Fin T → ℝ => objB (avgB c w₁ Z) - objB (0 : Vec d))
        (iidLaw noiseLaw T) ∧
      3 * c / (16 * (T : ℝ)) *
          (∑ t ∈ Finset.Icc (⌈max 2 (6 * c + 1)⌉₊ + 2) T, (1 : ℝ) / (t : ℝ))
          - max 2 (6 * c + 1) / (T : ℝ)
        ≤ ∫ Z, (objB (avgB c w₁ Z) - objB (0 : Vec d)) ∂(iidLaw noiseLaw T) := by sorry

end OptimalSGD.LowerBound
