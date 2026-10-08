-- Prove2me | Theorems.Thm_OnlineLearningOCO_Winnow_eq_3_4
-- name    : OnlineLearningOCO.Winnow.eq_3_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:55.161696+00:00
-- url     : https://prove2.me/theorems/cd4c3bfc-7223-4d18-a668-77500f5ea89e
-- title:
--   (3.4) — Winnow: $\sum_i w_t[i]z_t[i]^2\le 2f_t(w_t)$ for every round
-- statement:
--   Run Winnow with parameter $\eta$ on $(x_1,y_1),(x_2,y_2),\dots$ with $x_t\in\{0,1\}^d$ and $y_t\in\{-1,1\}$; let $\mathcal M$, $f_t$ and $z_t$ (with $z_t=-2y_tx_t$ on $t\in\mathcal M$, $0$ otherwise) be as in the Winnow definition. Then for every round $t$,
--   $$\sum_i w_t[i]\,z_t[i]^2\le 2f_t(w_t).$$
--
--   This bounds the local-norm term of (3.3) by the surrogate loss of the algorithm itself, which is what lets the mistake bound be solved for $\sum_t f_t(w_t)$.
--
--   **Formalization Note** $z_t[i]^2=4x_t[i]$ on error rounds whatever the sign convention, so the paper's erratum does not affect the left-hand side; the weights are those of the corrected Winnow. The statement holds for every real $\eta$, which includes the range $\eta\le1/2$ of Theorem 3.10. Rounds are numbered from $0$.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 175, §3.3.2, proof of Theorem 3.10, Equation (3.4)

import Mathlib
import Definitions.Def_OnlineLearningOCO_Winnow_Winnow
open Finset

namespace OnlineLearningOCO.Winnow

/-- Equation (3.4) (proof of Theorem 3.10, p. 175). For Winnow on instances `x_t ∈ {0,1}^d` and
labels `y_t ∈ {-1, 1}`, with `z_t = -2 y_t x_t · 1[t ∈ M]` and the surrogate `f_t`, every round
`t` satisfies `∑_i w_t[i] z_t[i]² ≤ 2 f_t(w_t)`. -/
theorem eq_3_4 (d : ℕ) (η : ℝ) (x : ℕ → Fin d → ℝ) (hx : ∀ t i, x t i = 0 ∨ x t i = 1)
    (y : ℕ → ℝ) (hy : ∀ t, y t = 1 ∨ y t = -1) (t : ℕ) :
    ∑ i, winnowWeights d η x y t i * winnowZ d η x y t i ^ 2 ≤
      2 * winnowSurrogate d η x y t (winnowWeights d η x y t) := by sorry

end OnlineLearningOCO.Winnow
