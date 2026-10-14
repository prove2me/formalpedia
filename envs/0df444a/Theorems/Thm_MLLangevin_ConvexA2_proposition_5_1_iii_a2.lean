-- Prove2me | Theorems.Thm_MLLangevin_ConvexA2_proposition_5_1_iii_a2
-- name    : MLLangevin.ConvexA2.proposition_5_1_iii_a2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:27.058977+00:00
-- url     : https://prove2.me/theorems/272a3efc-f6f6-4502-b5cf-a824932df972
-- title:
--   Proposition 5.1 (iii), (56) with 𝔞 = 2, p. 33 — (H₂) holds with c₂² ≲_uc (Lα⁻¹)⁴|b(x₀)|² + 𝔞₁|b(x₀)| + 𝔞₂d
-- statement:
--   There is a universal constant $\mathfrak c_u$ such that the following holds. Assume $(\mathbf C_\alpha)$, that $b$ is $L$-Lipschitz with $0<\alpha\le L$ and $\mathcal C^2$ with bounded partial derivatives up to order 2, $\sigma>0$ and $d\ge1$. Let $B^{(0)},B^{(1)},\dots$ be standard $d$-dimensional Brownian motions and $x_0\in\mathbb R^d$. Then there is a constant $c_2>0$ satisfying
--   $$c_2^2\le\mathfrak c_u\Big((L\alpha^{-1})^4|b(x_0)|^2+\mathfrak a_1|b(x_0)|+\mathfrak a_2d\Big), \tag{56}$$
--   such that assumption $(\mathbf H_2)$ holds with $\mathfrak a=2$ and this $c_2$ for every $\eta_0<\frac{\alpha}{2L^2}\wedge1$; that is, for every level $r$, every $\gamma\in(0,\frac{\alpha}{2L^2}\wedge1)$ and every $n\ge0$, $\|\bar X^{\gamma,x_0}_{n\gamma}-\bar X^{\gamma/2,x_0}_{n\gamma}\|_2\le c_2\gamma$, where both schemes are driven by $B^{(r)}$.
--
--   $(\mathbf H_2)$ with $\mathfrak a=2$ (an $L^2$ distance of order $\gamma$ between consecutive levels) is what allows the multilevel estimator to reach the cost $\varepsilon^{-2}$ without logarithmic factors.
--
--   **Formalization Note** The step range is that of Proposition 5.1, $\gamma\in(0,\frac{\alpha}{2L^2}\wedge1)$; since $(\mathbf H_2)$ is stated for $\gamma\in(0,\eta_0]$, the open range is written as "every $\eta_0<\frac{\alpha}{2L^2}\wedge1$", with one $c_2$ for all of them. The hypothesis $d\ge1$ is the paper's $\mathbb R^d$ with $d$ a positive integer; at $d=0$ with $b(x_0)=0$ the right side vanishes while $(\mathbf H_2)$ requires $c_2>0$. The regularity of §2.4.2 and $\sigma>0$ are carried as in Proposition 5.1(ii). The universal constant is quantified before every datum.
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Proposition 5.1 (iii), (56) second line, p. 33

import Mathlib
import Definitions.Def_MLLangevin_ConvexA2_Multilevel
import Definitions.Def_MLLangevin_ConvexA2_DriftNorms

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

theorem proposition_5_1_iii_a2 :
    ∃ cu : ℝ, ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℕ → ℝ≥0 → Ω → SDEState d), (∀ r, IsStandardBrownian P (B r)) →
      ∀ (b : SDEState d → SDEState d) (L α σ : ℝ),
      (∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖) → MLLangevin.ConvexA1.CondC b α → 0 < α → α ≤ L → C2Bounded b → 0 < σ →
      0 < d → ∀ x₀ : SDEState d,
        ∃ c₂ : ℝ, (∀ η₀ : ℝ, η₀ < min (α / (2 * L ^ 2)) 1 → H2 P b σ B x₀ η₀ 2 c₂) ∧
          c₂ ^ 2 ≤ cu * ((L / α) ^ 4 * ‖b x₀‖ ^ 2 + A1 b σ α L * ‖b x₀‖ + A2 b σ α L * d) := by sorry

end MLLangevin.ConvexA2
