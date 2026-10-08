-- Prove2me | Theorems.Thm_FracPackCover_Covering_theorem_3_7
-- name    : FracPackCover.Covering.theorem_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:50:09.668456+00:00
-- url     : https://prove2.me/theorems/bf454505-ffbe-4439-9a99-2636685e43e0
-- title:
--   Theorem 3.7 — an $\varepsilon$-relaxed decision procedure for fractional covering with $O(m+\rho\log^2m+\varepsilon^{-2}\rho\log(m/\varepsilon))$ oracle calls
-- statement:
--   Let $A\in\mathbb R^{m\times n}$ be nonnegative, $b>0$, and $P$ a nonempty convex set in the nonnegative orthant of $\mathbb R^n$. Let $\rho>0$ satisfy $a_ix\le\rho\,b_i$ for every $x\in P$ and every row $i$, and let subroutine (7) be any exact oracle that, given $y\ge0$, returns a point of $P$ maximizing $y^tAx$. Let $0<\varepsilon_0<1$ and put
--   $$N=m+\big(\lceil\log_2m\rceil+1\big)\big(2+4320\,\rho\ln(24m)\big)+2\big\lceil\log_2\varepsilon_0^{-1}\big\rceil+9408\,\rho\,\varepsilon_0^{-2}\ln\frac{24m}{\varepsilon_0}.$$
--   Then the covering algorithm of §3 (the initial solution of Lemma 3.6, calls to IMPROVE-COVER with $\varepsilon=1/6$, then $\varepsilon$-scaling) stops after at most $N$ calls to subroutine (7), and either
--   1. returns $x\in P$ with $Ax\ge(1-\varepsilon_0)b$ (an $\varepsilon_0$-approximate solution), or
--   2. reports that no exact solution exists, and indeed no $x\in P$ satisfies $Ax\ge b$.
--
--   This is the main result of §3: the fractional covering problem is decided, up to the relaxation $\varepsilon_0$, with a number of optimization-oracle calls that depends on the width $\rho$ but not on $n$ or on the structure of $P$.
--
--   **Formalization Note** The paper writes $O(m+\rho\log^2m+\varepsilon^{-2}\rho\log(m\varepsilon^{-1}))$; its proof yields the explicit $N$ above: $m$ calls for the initial solution, at most $\lceil\log_2m\rceil+1$ calls of IMPROVE-COVER with $\varepsilon=1/6$ at $2+4320\rho\ln(24m)$ oracle calls each (Theorem 3.5, part 1), and at most $\lceil\log_2\varepsilon_0^{-1}\rceil$ scaling phases whose costs (Theorem 3.5, part 2) sum to at most $2\lceil\log_2\varepsilon_0^{-1}\rceil+9408\rho\varepsilon_0^{-2}\ln(24m/\varepsilon_0)$. The time to compute $Ax$ between calls is not counted. Termination is asserted, not assumed: the algorithm, run with $\lceil N\rceil$ as the bound on every loop, returns an outcome. The quantification over every exact oracle and every width bound makes the bound uniform.
-- source:
--   Plotkin, Shmoys, Tardos, Fast Approximation Algorithms for Fractional Packing and Covering Problems, Cornell ORIE Tech. Rep. 999 (1992), p. 21, Theorem 3.7 (driver: pp. 20–21)

import Mathlib
import Definitions.Def_FracPackCover_Covering_Basic
import Definitions.Def_FracPackCover_Covering_ImproveCover
import Definitions.Def_FracPackCover_Covering_Driver

namespace FracPackCover.Covering

/-- Theorem 3.7 (Plotkin–Shmoys–Tardos, Cornell ORIE TR 999, p. 21), with the explicit constants
of its proof. For `0 < ε₀ < 1`, every covering instance (`A ≥ 0`, `b > 0`, `P` convex, nonempty, in
the nonnegative orthant), every width bound `ρ` and every exact maximization oracle, the covering
algorithm of §3 (`coverAlgorithm`: initial solution, phase `ε = 1/6`, `ε`-scaling) stops, using at most
`N = m + (⌈log₂ m⌉ + 1)(2 + 4320 ρ ln(24m)) + 2⌈log₂(1/ε₀)⌉ + 9408 ρ ε₀⁻² ln(24m/ε₀)` calls to
subroutine (7) (the paper writes `O(m + ρ log² m + ε⁻² ρ log(m ε⁻¹))`), and either returns `x ∈ P`
with `A x ≥ (1 − ε₀) b` or reports that no `x ∈ P` has `A x ≥ b`, correctly. -/
theorem theorem_3_7 {m n : ℕ} [NeZero m] (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (P : Set (Fin n → ℝ)) (hdata : IsCoveringData A b P) (ρ : ℝ) (hρ : WidthBound A b P ρ)
    (orc : (Fin m → ℝ) → (Fin n → ℝ)) (horc : IsMaxOracle A P orc)
    (ε₀ : ℝ) (hε₀ : 0 < ε₀) (hε₀1 : ε₀ < 1) :
    let N : ℝ := (m : ℝ) + ((⌈Real.logb 2 m⌉₊ : ℝ) + 1) * (2 + 4320 * ρ * Real.log (24 * m)) +
      2 * (⌈Real.logb 2 ε₀⁻¹⌉₊ : ℝ) + 9408 * ρ * ε₀⁻¹ ^ 2 * Real.log (24 * m * ε₀⁻¹)
    ∃ out : CoverOutcome n, ∃ c : ℕ,
      coverAlgorithm A b orc ρ ε₀ ⌈N⌉₊ = some (out, c) ∧ (c : ℝ) ≤ N ∧
      (∀ x, out = .approx x → x ∈ P ∧ ∀ i, (1 - ε₀) * b i ≤ rowVal A x i) ∧
      (out = .infeasible → ¬ ∃ x' ∈ P, ∀ i, b i ≤ rowVal A x' i) := by sorry

end FracPackCover.Covering
