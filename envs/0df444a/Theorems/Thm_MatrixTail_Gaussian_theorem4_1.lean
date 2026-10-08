-- Prove2me | Theorems.Thm_MatrixTail_Gaussian_theorem4_1
-- name    : MatrixTail.Gaussian.theorem4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T16:10:58.687593+00:00
-- url     : https://prove2.me/theorems/e4030737-c4b2-4de3-9fcf-a84dddf1240f
-- title:
--   Theorem 4.1 — matrix Gaussian and Rademacher series: P{λmax(Σ ξ_k A_k) ≥ t} ≤ d·e^{−t²/2σ²}, σ² = ‖Σ A_k²‖
-- statement:
--   Let $A_1,\dots,A_n$ be fixed self-adjoint complex $d\times d$ matrices ($d\ge1$), and let $\xi_1,\dots,\xi_n$ be independent random variables that are either all standard normal or all Rademacher. Define the variance parameter
--   $$\sigma^2 := \Big\|\sum_k A_k^2\Big\|.$$
--   Then for every $t\ge 0$:
--
--   1. $\displaystyle \mathbb P\Big\{\lambda_{\max}\Big(\sum_k \xi_k A_k\Big)\ge t\Big\}\le d\cdot e^{-t^2/2\sigma^2}$;
--   2. $\displaystyle \mathbb P\Big\{\Big\|\sum_k \xi_k A_k\Big\|\ge t\Big\}\le 2d\cdot e^{-t^2/2\sigma^2}$.
--
--   This is the noncommutative extension of the scalar Gaussian series bound $\mathbb P\{\sum_k\gamma_ka_k\ge t\}\le e^{-t^2/2\sigma^2}$ with $\sigma^2=\sum_k a_k^2$. The variance parameter is the norm of the sum of the squares, not the sum of their norms, and the price of the matrix setting is only the dimensional factor $d$.
--
--   **Formalization Note** $\|\cdot\|$ is the spectral norm. The two laws are two alternative hypotheses (all Gaussian, or all Rademacher), not a mixture. When $\sigma^2=0$ Lean's convention $x/0=0$ makes the right-hand sides $d$ and $2d$, a valid (trivial) bound; no positivity hypothesis on $\sigma^2$ is imposed.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, p. 14, Theorem 4.1, displays (4.2)–(4.4)

import Mathlib
import Definitions.Def_MatrixTail_Gaussian_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Gaussian

/-- **Theorem 4.1** (Matrix Gaussian and Rademacher Series), Tropp, arXiv:1004.4389v7, p. 14, displays
(4.2)–(4.4). Let `A₀, …, A_{n-1}` be fixed self-adjoint `d × d` matrices and `ξ₀, …, ξ_{n-1}` independent
scalar random variables that are either all standard normal or all Rademacher. With the variance parameter
`σ² := ‖Σ_k A_k²‖` (4.2), for all `t ≥ 0`:
* (4.3) `P{λmax(Σ_k ξ_k A_k) ≥ t} ≤ d · e^{−t²/2σ²}`;
* (4.4) `P{‖Σ_k ξ_k A_k‖ ≥ t} ≤ 2d · e^{−t²/2σ²}`.

Formalization Note.
* Complex Hermitian matrices; `‖·‖` is the spectral norm `specNorm`; `[NeZero d]` (at `d = 0` the right
  sides vanish while the probability at `t = 0` is `1`).
* "Gaussian or Rademacher" is the disjunction of two universal statements: the paper's sequence is all
  standard normal or all Rademacher, never a mixture.
* σ² is the norm of the sum, `specNorm (∑ k, A k ^ 2)`, not the sum of the norms.
* Boundary `σ² = 0`: Lean's `x / 0 = 0` makes the right sides `d` and `2d`, which are valid (and, at
  `t = 0`, the paper's values); for `t > 0` the paper's convention `e^{−∞} = 0` would give `0`, so at this
  degenerate point (all `A_k = 0`) the Lean bound is the trivial one. No positivity hypothesis is added. -/
theorem theorem4_1 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (A : Fin n → Matrix (Fin d) (Fin d) ℂ) (hAherm : ∀ k, (A k).IsHermitian)
    (ξ : Fin n → Ω → ℝ) (hindep : iIndepFun ξ P)
    (hlaw : (∀ k, IsStdGaussian P (ξ k)) ∨ (∀ k, IsRademacher P (ξ k))) :
    ∀ t : ℝ, 0 ≤ t →
      P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, ξ k ω • A k)} ≤
          d * Real.exp (-t ^ 2 / (2 * specNorm (∑ k, A k ^ 2))) ∧
        P.real {ω | t ≤ specNorm (∑ k, ξ k ω • A k)} ≤
          2 * d * Real.exp (-t ^ 2 / (2 * specNorm (∑ k, A k ^ 2))) := by sorry

end MatrixTail.Gaussian
