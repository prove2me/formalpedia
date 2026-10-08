-- Prove2me | Theorems.Thm_MatrixTail_Bernstein_theorem6_1_i
-- name    : MatrixTail.Bernstein.theorem6_1_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:06.961976+00:00
-- url     : https://prove2.me/theorems/095b0f0f-33e8-475c-9a93-b28d3ee84778
-- title:
--   Theorem 6.1(i) — matrix Bennett inequality: P{λmax(Σ X_k) ≥ t} ≤ d · exp(−(σ²/R²) · h(Rt/σ²))
-- statement:
--   Let $X_1,\dots,X_n$ be independent random self-adjoint $d\times d$ complex matrices, $d\ge1$, such that
--   $$\mathbb E X_k=0\qquad\text{and}\qquad\lambda_{\max}(X_k)\le R\ \text{almost surely},$$
--   and let $\sigma^2:=\big\|\sum_k\mathbb E(X_k^2)\big\|$ be the spectral norm of the total variance. Assume $R>0$ and $\sigma^2>0$. Then for every $t\ge0$,
--   $$\mathbb P\Big\{\lambda_{\max}\Big(\sum_k X_k\Big)\ge t\Big\}\le d\cdot\exp\Big(-\frac{\sigma^2}{R^2}\cdot h\Big(\frac{Rt}{\sigma^2}\Big)\Big),$$
--   where $h(u)=(1+u)\log(1+u)-u$.
--
--   This is the first link of the chain in Theorem 6.1, the matrix version of Bennett's inequality, with Poisson-type decay in the tail; the paper's proof isolates it as the main step, the other links being numerical.
--
--   **Formalization Note** $R>0$ and $\sigma^2>0$ are implicit in the printed formula, which divides by both; $R>0$ already follows from $\sigma^2>0$ and the other hypotheses. The entries of $X_k$ and $X_k^2$ are assumed integrable (the paper's standing regularity). No lower bound is placed on the eigenvalues of $X_k$.
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, pp. 23–24, Theorem 6.1, part (i); proof on p. 26

import Mathlib
import Definitions.Def_MatrixTail_Bernstein_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Bernstein

/-- **Theorem 6.1(i)** (the matrix Bennett inequality), Tropp, arXiv:1004.4389v7, pp. 23–24; its proof (p. 26)
isolates it: "The main challenge is to establish the Bennett inequality, Part (i)".
Let `X_1, …, X_n` (indexed by `Fin n`) be independent random self-adjoint `d × d` complex matrices with `E X_k = 0` and
`λmax(X_k) ≤ R` almost surely, and `σ² := ‖Σ_k E(X_k²)‖`. Then for all `t ≥ 0`,
`P{λmax(Σ_k X_k) ≥ t} ≤ d · exp(−(σ²/R²) · h(Rt/σ²))` with `h(u) = (1 + u) log(1 + u) − u`.

Formalization Note: `σ² = MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2))` is the spectral norm of the sum of the
second moments, as printed. `λmax(X_k) ≤ R` is assumed almost surely, as printed; no lower bound on the
eigenvalues is assumed. The hypotheses `0 < R` and `0 < σ²` are implicit in the printed formulas, which divide by
both (and `h` is defined only for `u ≥ 0`); `0 < R` is in fact implied by `0 < σ²` together with `E X_k = 0`
and `λmax(X_k) ≤ R`. At `σ² = 0` Lean's `x / 0 = 0` would replace the printed quotients by `0`. The entries of `X_k` and
`X_k²` are integrable (the §2.2 regularity: `E X_k` and `E(X_k²)` exist; otherwise `E(X_k²)` would be junk `0`).
Matrices are complex, independence is `iIndepFun`, `[NeZero d]` encodes dimension `d ≥ 1`. -/
theorem theorem6_1_i {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {n d : ℕ} [NeZero d] (X : Fin n → Ω → Matrix (Fin d) (Fin d) ℂ)
    (hX_meas : ∀ k, Measurable (X k)) (hX_herm : ∀ k ω, (X k ω).IsHermitian)
    (hX_indep : iIndepFun X P)
    (hX_int : ∀ k, MatrixTail.Master.MatIntegrable P (X k)) (hX2_int : ∀ k, MatrixTail.Master.MatIntegrable P (fun ω => X k ω ^ 2))
    (hX_mean : ∀ k, MatrixTail.Master.mean P (X k) = 0)
    (R : ℝ) (hX_max : ∀ k, ∀ᵐ ω ∂P, MatrixTail.Master.lambdaMax (X k ω) ≤ R)
    (hR : 0 < R) (hσ2 : 0 < MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)))
    (t : ℝ) (ht : 0 ≤ t) :
    P.real {ω | t ≤ MatrixTail.Master.lambdaMax (∑ k, X k ω)} ≤
      (d : ℝ) * Real.exp (-(MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)) / R ^ 2) *
        bennettH (R * t / MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)))) := by sorry

end MatrixTail.Bernstein
