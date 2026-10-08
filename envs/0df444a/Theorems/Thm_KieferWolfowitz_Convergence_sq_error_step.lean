-- Prove2me | Theorems.Thm_KieferWolfowitz_Convergence_sq_error_step
-- name    : KieferWolfowitz.Convergence.sq_error_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T12:48:10.771156+00:00
-- url     : https://prove2.me/theorems/42754307-b9ce-450e-860b-5756c0ccbf3d
-- title:
--   (3.6), p. 464 — $b_{n+1}=b_n+2\frac{a_n}{c_n}(P_n+N_n)+\frac{a_n^2}{c_n^2}e_n$
-- statement:
--   Let $H$ satisfy the variance bound (2.2) with constant $S$, let its regression function $M$ satisfy Condition 2 with constants $\rho,R>0$, let $a_n,c_n>0$, and let $(z_n,y_{2n-1},y_{2n})$ be a Kiefer–Wolfowitz process (2.7). Fix any real $\theta$ and write
--   $$b_n=E(z_n-\theta)^2,\quad U_n(z)=(z-\theta)\big(M(z+c_n)-M(z-c_n)\big),\quad e_n=E(y_{2n}-y_{2n-1})^2 .$$
--   Then $(z_n-\theta)^2$, $U_n(z_n)$ and $(y_{2n}-y_{2n-1})^2$ are integrable, and
--   $$b_{n+1}=b_n+2\,\frac{a_n}{c_n}\,E\,U_n(z_n)+\frac{a_n^2}{c_n^2}\,e_n .$$
--
--   Since $E\,U_n(z_n)=P_n+N_n$ with $P_n=E\,U_n^+(z_n)$ and $N_n=E\,U_n^-(z_n)$, this is the paper's (3.6). It is the basic recursion of the mean squared error from which the whole proof proceeds.
--
--   **Formalization Note** The statement uses $E\,U_n(z_n)$ in place of $P_n+N_n$ (equal since $U_n=U_n^++U_n^-$). The identity holds for every $\theta$, not only the maximizer, and needs neither unimodality nor Conditions 1, 3; Condition 2 bounds the drift and makes the expectations finite. The paper's $b_n$ is tacitly finite; here integrability is part of the conclusion. Lean index $n$ is the paper's $n+1$.
-- source:
--   Kiefer & Wolfowitz, Stochastic estimation of the maximum of a regression function, Ann. Math. Statist. 23 (1952), p. 463, (3.1)–(3.5); p. 464, (3.6)

import Mathlib
import Definitions.Def_KieferWolfowitz_Convergence_Model

open MeasureTheory ProbabilityTheory Filter Topology

namespace KieferWolfowitz.Convergence

/-- Kiefer & Wolfowitz (1952), (3.6), p. 464: the one-step identity
`b_{n+1} = b_n + 2 (a_n/c_n)(P_n + N_n) + (a_n²/c_n²) e_n`, with `P_n + N_n = E U_n(z_n)`,
together with the integrability of every expectation in it. -/
theorem sq_error_step {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℕ mΩ)
    (H : Kernel ℝ ℝ) [IsMarkovKernel H] (S θ : ℝ)
    (hS : SecondMomentBound H S)
    (ρ R : ℝ) (hρ : 0 < ρ) (hR : 0 < R) (h2 : Cond2 (regFun H) ρ R)
    (a c : ℕ → ℝ) (ha : ∀ n, 0 < a n) (hc : ∀ n, 0 < c n) (z₁ : ℝ)
    (z yminus yplus : ℕ → Ω → ℝ) (hz : IsKWProcess H a c z₁ P ℱ z yminus yplus) (n : ℕ) :
    Integrable (fun ω => (z n ω - θ) ^ 2) P ∧
    Integrable (fun ω => U (regFun H) θ (c n) (z n ω)) P ∧
    Integrable (fun ω => (yplus n ω - yminus n ω) ^ 2) P ∧
    ∫ ω, (z (n + 1) ω - θ) ^ 2 ∂P =
      ∫ ω, (z n ω - θ) ^ 2 ∂P + 2 * (a n / c n) * ∫ ω, U (regFun H) θ (c n) (z n ω) ∂P
        + a n ^ 2 / c n ^ 2 * ∫ ω, (yplus n ω - yminus n ω) ^ 2 ∂P := by sorry

end KieferWolfowitz.Convergence
