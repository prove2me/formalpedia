-- Prove2me | Theorems.Thm_OnlineLearningOCO_Winnow_theorem_2_23
-- name    : OnlineLearningOCO.Winnow.theorem_2_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T14:23:18.37427+00:00
-- url     : https://prove2.me/theorems/29d7ec09-11b1-4276-9dcb-9938fe389bce
-- title:
--   Theorem 2.23 — unnormalized EG has regret $\le(d\lambda+\sum_i u[i]\log(u[i]/(e\lambda)))/\eta+\eta\sum_t\sum_i w_t[i]z_t[i]^2$
-- statement:
--   Let $\eta,\lambda>0$ and run unnormalized EG in dimension $d$ on linear losses $z_1,\dots,z_T\in\mathbb R^d$ with $\eta z_t[i]\ge-1$ for all $t,i$; write $w_t$ for its weights. Then for every $u\in\mathbb R^d$ with $u\ge 0$,
--   $$\sum_{t=1}^T\langle w_t-u,z_t\rangle\le\frac{d\lambda+\sum_{i=1}^d u[i]\log\bigl(u[i]/(e\lambda)\bigr)}{\eta}+\eta\sum_{t=1}^T\sum_{i=1}^d w_t[i]\,z_t[i]^2 .$$
--   In particular, if $d\ge1$ and $\lambda=1/d$,
--   $$\sum_{t=1}^T\langle w_t-u,z_t\rangle\le\frac{1+(\log d-1)\|u\|_1+\sum_{i=1}^d u[i]\log u[i]}{\eta}+\eta\sum_{t=1}^T\sum_{i=1}^d w_t[i]\,z_t[i]^2 .$$
--   Here $\log$ is the natural logarithm and $0\log 0=0$.
--
--   This is a local-norm regret bound: the second term weighs each squared loss by the current weight. It is the bound Winnow's mistake bound is derived from.
--
--   **Formalization Note** $0\log 0=0$ holds in Lean because `Real.log 0 = 0`, so coordinates with $u[i]=0$ contribute nothing, as in the entropy convention. $\|u\|_1$ is written $\sum_i u[i]$, which equals it because $u\ge0$. The second display is stated under $0<d$, needed for $\lambda=1/d>0$. Rounds are numbered $0,\dots,T-1$.
-- source:
--   Shalev-Shwartz, Online Learning and Online Convex Optimization, Found. Trends Mach. Learn. 4(2) (2011) 107–194, p. 154, Theorem 2.23 (proof p. 155)

import Mathlib
import Definitions.Def_OnlineLearningOCO_Winnow_uegWeights
open Finset

namespace OnlineLearningOCO.Winnow

/-- Theorem 2.23 (p. 154). Unnormalized EG with parameters `η, λ > 0` on linear losses with
`η z_t[i] ≥ -1` satisfies, for every `u ≥ 0`,
`∑_t ⟨w_t - u, z_t⟩ ≤ (dλ + ∑_i u[i] log(u[i]/(eλ)))/η + η ∑_t ∑_i w_t[i] z_t[i]²`,
and, with `λ = 1/d`,
`∑_t ⟨w_t - u, z_t⟩ ≤ (1 + (log d - 1)‖u‖₁ + ∑_i u[i] log u[i])/η + η ∑_t ∑_i w_t[i] z_t[i]²`.
Rounds are numbered from `0`; `0 · log 0 = 0` through `Real.log 0 = 0`. -/
theorem theorem_2_23 {d : ℕ} (η lam : ℝ) (hη : 0 < η) (hlam : 0 < lam) (z : ℕ → Fin d → ℝ)
    (hz : ∀ t i, -1 ≤ η * z t i) (u : Fin d → ℝ) (hu : ∀ i, 0 ≤ u i) (T : ℕ) :
    (∑ t ∈ range T, ∑ i, (uegWeights η lam z t i - u i) * z t i ≤
      ((d : ℝ) * lam + ∑ i, u i * Real.log (u i / (Real.exp 1 * lam))) / η +
        η * ∑ t ∈ range T, ∑ i, uegWeights η lam z t i * z t i ^ 2) ∧
    (0 < d →
      ∑ t ∈ range T, ∑ i, (uegWeights η (1 / (d : ℝ)) z t i - u i) * z t i ≤
        (1 + (Real.log d - 1) * ∑ i, u i + ∑ i, u i * Real.log (u i)) / η +
          η * ∑ t ∈ range T, ∑ i, uegWeights η (1 / (d : ℝ)) z t i * z t i ^ 2) := by sorry

end OnlineLearningOCO.Winnow
