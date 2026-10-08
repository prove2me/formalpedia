-- Prove2me | Theorems.Thm_KalaiVempala_Multiplicative_eq_7
-- name    : KalaiVempala.Multiplicative.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T07:53:15.308762+00:00
-- url     : https://prove2.me/theorems/1729b385-b581-4991-8ae6-4f0d1769a80c
-- title:
--   Eq. (7), p. 303 — E[M(s_{1:t−1}+p)·s_t] = ∫ (M(s_{1:t}+y)·s_t) e^{−ε(|y+s_t|₁−|y|₁)} dμ(y)
-- statement:
--   Let $\varepsilon > 0$, let $\mu_\varepsilon$ be the FPL\* perturbation law on $\mathbb R^n$ (density $(\varepsilon/2)^n e^{-\varepsilon|x|_1}$), let $M : \mathbb R^n \to \mathbb R^n$ be measurable, let $s_1, s_2, \dots \in \mathbb R^n$ and $t \ge 1$. Then
--   $$\int_{\mathbb R^n} M(s_{1:t-1} + x)\cdot s_t \, d\mu_\varepsilon(x) \;=\; \int_{\mathbb R^n} \big(M(s_{1:t} + y)\cdot s_t\big)\, e^{-\varepsilon(|y + s_t|_1 - |y|_1)}\, d\mu_\varepsilon(y).$$
--
--   The identity compares FPL\*, which uses $s_{1:t-1}$, with the "be the perturbed leader" algorithm, which uses $s_{1:t}$: the two expectations differ only through the ratio of the densities of $\mu_\varepsilon$ at $y + s_t$ and at $y$.
--
--   **Formalization Note** The identity holds for every measurable $M$ and every real state sequence: the oracle property, the nonnegativity of $\mathcal D, \mathcal S$ and the parameters $D, R, A$ are not used and are not hypotheses. Measurability of $M$ is added, as in every statement of the mission, because the expectations presuppose it. The condition $t \ge 1$ makes $s_{1:t} = s_{1:t-1} + s_t$.
-- source:
--   Kalai & Vempala, Efficient algorithms for online decision problems, J. Comput. System Sci. 71 (2005), p. 303, display (7)

import Mathlib
import Definitions.Def_OracleRO_ApproxFPL_FPL
import Definitions.Def_KalaiVempala_Multiplicative_Setting

open MeasureTheory OracleRO.ApproxFPL

namespace KalaiVempala.Multiplicative

theorem eq_7 {n : ℕ} (M : (Fin n → ℝ) → (Fin n → ℝ)) (hMmeas : Measurable M)
    (s : ℕ → Fin n → ℝ) (ε : ℝ) (hε : 0 < ε) (t : ℕ) (ht : 1 ≤ t) :
    ∫ x, M (prefixSum s (t - 1) + x) ⬝ᵥ s t ∂(laplaceLaw n ε) =
      ∫ y, (M (prefixSum s t + y) ⬝ᵥ s t) *
          Real.exp (-(ε * (∑ i, |y i + s t i| - ∑ i, |y i|))) ∂(laplaceLaw n ε) := by sorry

end KalaiVempala.Multiplicative
