-- Prove2me | Theorems.Thm_OnlineLearningOCO_Winnow_eq_3_3
-- name    : OnlineLearningOCO.Winnow.eq_3_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:46.980028+00:00
-- url     : https://prove2.me/theorems/f157aec5-7fe9-42d3-8830-684614739925
-- title:
--   (3.3) — Winnow: $\sum_t(f_t(w_t)-f_t(u))\le\sum_t\langle w_t-u,z_t\rangle\le k\log(d)/\eta+\eta\sum_t\sum_i w_t[i]z_t[i]^2$
-- statement:
--   Run Winnow with parameter $0<\eta\le1/2$ on $(x_1,y_1),\dots,(x_T,y_T)$ with $x_t\in\{0,1\}^d$ and $y_t\in\{-1,1\}$; let $\mathcal M$ be its error rounds, $f_t(w)=\mathbf 1_{[t\in\mathcal M]}[1-y_t(2\langle w,x_t\rangle-1)]_+$ its surrogate losses and $z_t=-2y_tx_t$ for $t\in\mathcal M$, $z_t=0$ otherwise. Then for every $u\in\{0,1\}^d$ with $\|u\|_1=k\ge1$,
--   $$\sum_{t=1}^T\bigl(f_t(w_t)-f_t(u)\bigr)\le\sum_{t=1}^T\langle w_t-u,z_t\rangle\le\frac{k\log d}{\eta}+\eta\sum_{t=1}^T\sum_i w_t[i]\,z_t[i]^2 .$$
--
--   The first inequality is the subgradient inequality for the surrogates; the second is Theorem 2.23 with $\lambda=1/d$ specialised to Boolean comparators. Together with (3.4) it yields Theorem 3.10.
--
--   **Formalization Note** $z_t$ carries the corrected sign $-2y_tx_t$ (the paper prints $2y_tx_t$; see the Winnow definition). The hypotheses $1\le k$ and $\eta\le1/2$ come from the page: $1+k\log(d/e)\le k\log d$ needs $k\ge1$, and Theorem 3.10 assumes $\eta\le1/2$, which gives $\eta z_t[i]\ge-1$. The sequence hypotheses are stated for all rounds (a finite sequence extends to an infinite one). Rounds are numbered $0,\dots,T-1$.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 174, §3.3.2, proof of Theorem 3.10, Equation (3.3)

import Mathlib
import Definitions.Def_OnlineLearningOCO_Winnow_Winnow
open Finset

namespace OnlineLearningOCO.Winnow

/-- Equation (3.3) (proof of Theorem 3.10, p. 174). For Winnow with `0 < η ≤ 1/2` on instances
`x_t ∈ {0,1}^d` and labels `y_t ∈ {-1, 1}`, with `z_t = -2 y_t x_t · 1[t ∈ M]`, and for every
`u ∈ {0,1}^d` with `‖u‖₁ = k ≥ 1`,
`∑_t (f_t(w_t) - f_t(u)) ≤ ∑_t ⟨w_t - u, z_t⟩ ≤ k log(d)/η + η ∑_t ∑_i w_t[i] z_t[i]²`.
Rounds `0, …, T-1` stand for the paper's `1, …, T`. -/
theorem eq_3_3 (d k : ℕ) (hk : 1 ≤ k) (η : ℝ) (hη : 0 < η) (hη2 : η ≤ 1 / 2)
    (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1)
    (u : Fin d → ℝ) (hu : ∀ i, u i = 0 ∨ u i = 1) (hu1 : ∑ i, u i = (k : ℝ)) (T : ℕ) :
    ∑ t ∈ range T, (winnowSurrogate d η x y t (winnowWeights d η x y t) -
        winnowSurrogate d η x y t u) ≤
      ∑ t ∈ range T, ∑ i, (winnowWeights d η x y t i - u i) * winnowZ d η x y t i ∧
    ∑ t ∈ range T, ∑ i, (winnowWeights d η x y t i - u i) * winnowZ d η x y t i ≤
      (k : ℝ) * Real.log d / η +
        η * ∑ t ∈ range T, ∑ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 := by sorry

end OnlineLearningOCO.Winnow
