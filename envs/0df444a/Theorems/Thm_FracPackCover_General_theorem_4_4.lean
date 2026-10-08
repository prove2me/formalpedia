-- Prove2me | Theorems.Thm_FracPackCover_General_theorem_4_4
-- name    : FracPackCover.General.theorem_4_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:22:22.064495+00:00
-- url     : https://prove2.me/theorems/c5c0a244-168c-4a8f-b6c7-a07943b9c2a4
-- title:
--   Theorem 4.4 — IMPROVE-GENERAL stops after at most 2 + 8640ρ²λ₀⁻²ln(12mρλ₀⁻¹) oracle calls
-- statement:
--   Let $A, b, d > 0, P$ be as in the GENERAL problem with $P$ convex, let $\rho > 0$ bound the width ($|a_i x - b_i| \le \rho d_i$ on $P$), and let $\mathrm{orc}$ be any exact minimizing oracle (subroutine (10)). Let $x_0 \in P$ with $\lambda_0 = \lambda(x_0) > 0$. Then procedure IMPROVE-GENERAL started at $x_0$, with parameters $\alpha = 4\lambda_0^{-1}\ln(12m\rho\lambda_0^{-1})$ and $\sigma = \lambda_0/(48\alpha\rho^2)$, stops, and the number of oracle calls it makes is at most
--   $$B = 2 + 8640\,\frac{\rho^2}{\lambda_0^2}\,\ln\!\Big(\frac{12 m\rho}{\lambda_0}\Big).$$
--   More precisely, run with any fuel $F \ge B$, the loop test fails before the fuel is exhausted.
--
--   This is the per-call complexity bound that the driver's analysis sums over the calls.
--
--   **Formalization Note.** The paper writes $O(\rho^2\lambda_0^{-2}\log(m\rho\lambda_0^{-1}))$ iterations; its proof (Lemma 4.3 with $\lambda \ge \lambda_0/2$, $e^{\alpha\lambda_0/2} \le \Phi \le m e^{\alpha\lambda_0}$) yields at most $1 + 8640\rho^2\lambda_0^{-2}\ln(12m\rho\lambda_0^{-1})$ updates and one more oracle call. The statement is for the corrected parameters ($\lambda_0/2$ in place of $\lambda_0$ in Figure 4's $\alpha$ and $\sigma$); with Figure 4's printed parameters the hypothesis $\sigma \le \lambda/(24\alpha\rho^2)$ of Lemma 4.3 fails whenever $\lambda < \lambda_0$, and the decrease its proof gives is negative for $\lambda < 5\lambda_0/6$.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), p. 27, Theorem 4.4 (for Figure 4 with λ₀/2-corrected parameters)

import Mathlib
import Definitions.Def_FracPackCover_General_Improve

namespace FracPackCover.General

/-- Theorem 4.4 (p. 27), for IMPROVE-GENERAL with the corrected parameters
`α = 4λ₀⁻¹ ln(12mρλ₀⁻¹)`, `σ = λ₀/(48αρ²)`. Started at `x₀ ∈ P` with `λ₀ = λ(x₀) > 0`, every
exact minimizing oracle, the procedure stops (its loop test fails) within
`B = 2 + 8640 ρ² λ₀⁻² ln(12mρλ₀⁻¹)` loop tests and makes at most `B` oracle calls (the paper writes
`O(ρ²λ₀⁻² log(mρλ₀⁻¹))` iterations). -/
theorem theorem_4_4 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMinOracle P A orc)
    (x0 : Fin n → ℝ) (hx0 : x0 ∈ P) (hlam : 0 < lam A b d x0) (fuel : ℕ)
    (hfuel : 2 + 8640 * ρ ^ 2 / lam A b d x0 ^ 2 * Real.log (12 * m * ρ / lam A b d x0)
      ≤ (fuel : ℝ)) :
    (improveGeneral A b d ρ orc fuel x0).exit ≠ ImproveExit.outOfFuel ∧
      ((improveGeneral A b d ρ orc fuel x0).calls : ℝ) ≤
        2 + 8640 * ρ ^ 2 / lam A b d x0 ^ 2 * Real.log (12 * m * ρ / lam A b d x0) := by sorry

end FracPackCover.General
