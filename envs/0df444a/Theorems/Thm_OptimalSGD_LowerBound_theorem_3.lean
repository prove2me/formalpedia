-- Prove2me | Theorems.Thm_OptimalSGD_LowerBound_theorem_3
-- name    : OptimalSGD.LowerBound.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:24:32.096407+00:00
-- url     : https://prove2.me/theorems/b5f377a8-c2cf-44ed-8aff-4184eea2afdc
-- title:
--   Theorem 3 — averaged SGD on [0,1]^d: E[F(w̄_T) − F(w*)] ≥ (c/16T) Σ_{t=T₀}^{T−1} 1/t
-- statement:
--   Consider Example A: the domain $W=[0,1]^d$, the $1$-strongly convex objective $F(w)=\tfrac12\|w\|^2+w_1$ (where $w_1$ is the first coordinate of $w$), whose global minimum over $W$ is $w^*=0$, and the stochastic gradient oracle that at the query point $w_t$ returns $\hat g_t=w_t+(Z_t,0,\dots,0)$, with $Z_1,Z_2,\dots$ independent and uniformly distributed on $[-1,3]$.
--
--   Let $c>0$, and run projected SGD $w_{t+1}=\Pi_W(w_t-\eta_t\hat g_t)$ with step sizes $\eta_t=c/t$ from an arbitrary starting point $w_1\in W$. Let $\bar w_T=\frac1T(w_1+\dots+w_T)$ and $T_0=\max\{2,c/2\}$. Then for every integer $T\ge T_0+1$,
--   $$\mathbb E\big[F(\bar w_T)-F(w^*)\big]\ \ge\ \frac{c}{16T}\sum_{t=T_0}^{T-1}\frac1t,$$
--   where the sum runs over the integers $t$ with $T_0\le t\le T-1$. For fixed $c$ the right-hand side is of order $\log(T)/T$.
--
--   This is the paper's first example: since the minimizer lies at a corner of the domain, the average of the iterates stays at distance of order $\log(T)/T$ in function value.
--
--   **Formalization Note** The expectation is the Bochner integral over the law $\mathrm{Unif}[-1,3]^{\otimes T}$ of $(Z_1,\dots,Z_T)$; the statement also asserts that $F(\bar w_T)-F(0)$ is integrable, so the integral is not a default value. $T_0$ is real; $T$ is a natural number with $T\ge T_0+1$, and the sum is over `Finset.Ico ⌈T₀⌉₊ T`. $d\ge1$, and $c>0$ is the only condition on $c$.
-- source:
--   Rakhlin, Shamir, Sridharan, Making Gradient Descent Optimal for Strongly Convex Stochastic Optimization, arXiv:1109.5647v7, p. 5, Theorem 3 (example on pp. 4–5; proof App. B.4, p. 15)

import Mathlib
import Definitions.Def_UnderstandingML_Framework
import Definitions.Def_UnderstandingML_Linear
import Definitions.Def_OptimalSGD_LowerBound_Model

namespace OptimalSGD.LowerBound

open MeasureTheory UnderstandingML

/-- **Theorem 3** (Rakhlin, Shamir, Sridharan, arXiv:1109.5647v7, p. 5). On Example A
(`W = [0, 1]^d`, `F(w) = ½‖w‖² + w₁`, oracle `ĝ = w + (Z, 0, …, 0)`, `Z ∼ Unif[−1, 3]` i.i.d.),
SGD initialized at any point of `W` and run with `η_t = c/t` satisfies, for every `T ≥ T₀ + 1`
with `T₀ = max{2, c/2}`, `E[F(w̄_T) − F(w*)] ≥ (c/(16T)) ∑_{t=T₀}^{T−1} 1/t`, where `w* = 0`.
The sum ranges over the integers `t` with `T₀ ≤ t ≤ T − 1`. -/
theorem theorem_3 (d : ℕ) [NeZero d] (c : ℝ) (hc : 0 < c) (w₁ : Vec d)
    (hw₁ : w₁ ∈ box 0 1) (T : ℕ) (hT : max 2 (c / 2) + 1 ≤ (T : ℝ)) :
    Integrable (fun Z : Fin T → ℝ => objA (avgA c w₁ Z) - objA (0 : Vec d))
        (iidLaw noiseLaw T) ∧
      c / (16 * (T : ℝ)) * (∑ t ∈ Finset.Ico ⌈max 2 (c / 2)⌉₊ T, (1 : ℝ) / (t : ℝ))
        ≤ ∫ Z, (objA (avgA c w₁ Z) - objA (0 : Vec d)) ∂(iidLaw noiseLaw T) := by sorry

end OptimalSGD.LowerBound
