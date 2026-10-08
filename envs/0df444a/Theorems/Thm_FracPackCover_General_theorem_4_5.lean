-- Prove2me | Theorems.Thm_FracPackCover_General_theorem_4_5
-- name    : FracPackCover.General.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T19:23:26.090369+00:00
-- url     : https://prove2.me/theorems/d081dee4-ee86-4cc6-aa14-2031d27f0807
-- title:
--   Theorem 4.5 — an ε-relaxed decision procedure for Ax ≤ b, x ∈ P with O(ρ²ε⁻²log(mρ/ε)) oracle calls
-- statement:
--   Let $A$ be an arbitrary real $m\times n$ matrix, $b \in \mathbb R^m$ arbitrary, $d \in \mathbb R^m$ with $d > 0$, and $P \subseteq \mathbb R^n$ convex. Let $\rho > 0$ bound the width, $|a_i x - b_i| \le \rho d_i$ for all $x \in P$ and all $i$, and let $\mathrm{orc}$ be any exact minimizing oracle for $P$ and $A$ (subroutine (10)). For every $\varepsilon$ with $0 < \varepsilon < 1$ and every starting point $x_0 \in P$, the driver that calls IMPROVE-GENERAL repeatedly:
--
--   1. stops;
--   2. if it outputs a point $x$, then $x \in P$ and $Ax \le b + \varepsilon d$ ($x$ is an $\varepsilon$-approximate solution);
--   3. if it reports infeasibility, then there is no exact solution: no $x \in P$ satisfies $Ax \le b$;
--   4. it makes at most
--   $$N = 2\big(\lfloor \log_2(\rho/\varepsilon)\rfloor + 1\big) + 11520\,\frac{\rho^2}{\varepsilon^2}\,\ln\!\Big(\frac{12\, m\, \max(\rho,\varepsilon)}{\varepsilon}\Big)$$
--   calls to subroutine (10).
--
--   This is the paper's main result for the GENERAL problem: an $\varepsilon$-relaxed decision procedure whose number of optimization-oracle calls depends on the width $\rho$, the accuracy $\varepsilon$ and only logarithmically on the number of constraints.
--
--   **Formalization Note.** The paper writes $O(\rho^2\varepsilon^{-2}\log(m\rho\varepsilon^{-1}))$; its proof yields $N$ above: each call made with $\lambda_0 > \varepsilon$ costs at most $2 + 8640\rho^2\lambda_0^{-2}\ln(12m\rho/\lambda_0)$ calls (Theorem 4.4), $\lambda_0$ more than halves between calls, so $\sum \lambda_0^{-2} < \tfrac43\varepsilon^{-2}$ and there are at most $\lfloor\log_2(\rho/\varepsilon)\rfloor + 1$ calls. The $\max(\rho,\varepsilon)$ equals $\rho$ whenever any call is made (it only keeps $N$ nonnegative when $\rho < \varepsilon$, a case in which every point of $P$ is already $\varepsilon$-approximate); $\lfloor\cdot\rfloor$ is the floor truncated at $0$. IMPROVE-GENERAL uses $\lambda_0/2$ in place of $\lambda_0$ in Figure 4's $\alpha$ and $\sigma$ (see the procedure's definition). The driver is run with a fuel bound, and the theorem asserts it stops for every fuel $\ge N$. The "time to compute $Ax$" part of the paper's statement is not formalized.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), p. 27, Theorem 4.5 (for Figure 4 with λ₀/2-corrected parameters)

import Mathlib
import Definitions.Def_FracPackCover_General_Driver

namespace FracPackCover.General

/-- Theorem 4.5 (p. 27), for the driver over IMPROVE-GENERAL with the corrected parameters.
For every `ε ∈ (0,1)`, every start `x₀ ∈ P` and every exact minimizing oracle, the driver run with
any fuel `≥ N` stops; if it outputs `x` then `x ∈ P` and `Ax ≤ b + εd`; if it reports
infeasibility then no `x ∈ P` has `Ax ≤ b`; and it makes at most
`N = 2(⌊log₂(ρ/ε)⌋ + 1) + 11520 ρ² ε⁻² ln(12 m max(ρ,ε)/ε)` oracle calls (the paper writes
`O(ρ²ε⁻² log(mρε⁻¹))`). -/
theorem theorem_4_5 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b d : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hP : Convex ℝ P) (hd : ∀ i, 0 < d i)
    (ρ : ℝ) (hρ : 0 < ρ) (hW : WidthBound A b d P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMinOracle P A orc)
    (x0 : Fin n → ℝ) (hx0 : x0 ∈ P) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1) (fuel : ℕ)
    (hfuel : 2 * ((⌊Real.logb 2 (ρ / ε)⌋₊ : ℝ) + 1)
        + 11520 * ρ ^ 2 / ε ^ 2 * Real.log (12 * m * max ρ ε / ε) ≤ (fuel : ℝ)) :
    (generalDriver A b d ρ ε orc fuel x0).outcome ≠ DriverOutcome.outOfFuel ∧
    (∀ x, (generalDriver A b d ρ ε orc fuel x0).outcome = DriverOutcome.approx x →
        x ∈ P ∧ ∀ i, FracPackCover.Covering.rowVal A x i ≤ b i + ε * d i) ∧
    ((generalDriver A b d ρ ε orc fuel x0).outcome = DriverOutcome.infeasible →
        ¬ ∃ x ∈ P, ∀ i, FracPackCover.Covering.rowVal A x i ≤ b i) ∧
    ((generalDriver A b d ρ ε orc fuel x0).calls : ℝ) ≤
        2 * ((⌊Real.logb 2 (ρ / ε)⌋₊ : ℝ) + 1)
          + 11520 * ρ ^ 2 / ε ^ 2 * Real.log (12 * m * max ρ ε / ε) := by sorry

end FracPackCover.General
