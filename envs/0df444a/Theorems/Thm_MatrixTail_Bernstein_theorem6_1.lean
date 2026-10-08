-- Prove2me | Theorems.Thm_MatrixTail_Bernstein_theorem6_1
-- name    : MatrixTail.Bernstein.theorem6_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T17:10:19.396687+00:00
-- url     : https://prove2.me/theorems/3faef472-2345-42be-b4e1-0258b30216f4
-- title:
--   Theorem 6.1 — matrix Bernstein, bounded case: the Bennett, Bernstein and split Bernstein chain
-- statement:
--   Let $X_1,\dots,X_n$ be independent random self-adjoint $d\times d$ complex matrices, $d\ge1$, such that
--   $$\mathbb E X_k=0\qquad\text{and}\qquad\lambda_{\max}(X_k)\le R\ \text{almost surely},$$
--   and let $\sigma^2:=\big\|\sum_k\mathbb E(X_k^2)\big\|$. Assume $R>0$ and $\sigma^2>0$, and let $h(u)=(1+u)\log(1+u)-u$. Then for every $t\ge0$ the following chain holds:
--   $$\begin{aligned}
--   \mathbb P\Big\{\lambda_{\max}\Big(\sum_k X_k\Big)\ge t\Big\}
--   &\le d\cdot\exp\Big(-\frac{\sigma^2}{R^2}\, h\Big(\frac{Rt}{\sigma^2}\Big)\Big) &&\text{(i)}\\
--   &\le d\cdot\exp\Big(\frac{-t^2/2}{\sigma^2+Rt/3}\Big) &&\text{(ii)}\\
--   &\le\begin{cases} d\cdot\exp(-3t^2/8\sigma^2), & t\le\sigma^2/R,\\ d\cdot\exp(-3t/8R), & t\ge\sigma^2/R.\end{cases} &&\text{(iii)}
--   \end{aligned}$$
--
--   Part (i) is the matrix Bennett inequality, (ii) the matrix Bernstein inequality, and (iii) the split form, which separates subgaussian behaviour at moderate deviations from subexponential decay in the tail. Only the largest eigenvalue of each summand is bounded; the smallest may be arbitrarily negative.
--
--   **Formalization Note** The chain is stated as a conjunction: the probability is at most (i); (i) is at most (ii); and (ii) is at most each branch of (iii) on its range of $t$ (both ranges contain $t=\sigma^2/R$, as printed). $R>0$ and $\sigma^2>0$ are implicit in the printed formulas, which divide by both. The entries of $X_k$ and $X_k^2$ are assumed integrable (the paper's standing regularity).
-- source:
--   Tropp, User-Friendly Tail Bounds for Sums of Random Matrices, arXiv:1004.4389v7, pp. 23–24, Theorem 6.1 (Matrix Bernstein: Bounded Case)

import Mathlib
import Definitions.Def_MatrixTail_Bernstein_Model

open MeasureTheory ProbabilityTheory
open scoped MatrixOrder ComplexOrder ENNReal

namespace MatrixTail.Bernstein

/-- **Theorem 6.1** (Matrix Bernstein: Bounded Case), Tropp, arXiv:1004.4389v7, pp. 23–24.
Let `X_1, …, X_n` (indexed by `Fin n`) be independent random self-adjoint `d × d` complex matrices with `E X_k = 0` and
`λmax(X_k) ≤ R` almost surely, and `σ² := ‖Σ_k E(X_k²)‖`. Then for all `t ≥ 0` the chain holds:
`P{λmax(Σ_k X_k) ≥ t} ≤ d · exp(−(σ²/R²) · h(Rt/σ²))` (i)
`≤ d · exp((−t²/2)/(σ² + Rt/3))` (ii)
`≤ d · exp(−3t²/8σ²)` for `t ≤ σ²/R` and `≤ d · exp(−3t/8R)` for `t ≥ σ²/R` (iii),
with `h(u) = (1 + u) log(1 + u) − u`.

Formalization Note: the chain is stated as the conjunction P ≤ (i), (i) ≤ (ii), and each case of (iii)
with its range of `t` as a hypothesis (both ranges include `t = σ²/R`, as printed).
Formalization Note: `σ² = MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2))` is the spectral norm of the sum of the
second moments, as printed. `λmax(X_k) ≤ R` is assumed almost surely, as printed; no lower bound on the
eigenvalues is assumed. The hypotheses `0 < R` and `0 < σ²` are implicit in the printed formulas, which divide by
both (and `h` is defined only for `u ≥ 0`); `0 < R` is in fact implied by `0 < σ²` together with `E X_k = 0`
and `λmax(X_k) ≤ R`. At `σ² = 0` Lean's `x / 0 = 0` would make the chain false. The entries of `X_k` and
`X_k²` are integrable (the §2.2 regularity: `E X_k` and `E(X_k²)` exist; otherwise `E(X_k²)` would be junk `0`).
Matrices are complex, independence is `iIndepFun`, `[NeZero d]` encodes dimension `d ≥ 1`. -/
theorem theorem6_1 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
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
          bennettH (R * t / MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)))) ∧
      (d : ℝ) * Real.exp (-(MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)) / R ^ 2) *
          bennettH (R * t / MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)))) ≤
        (d : ℝ) * Real.exp (-(t ^ 2 / 2) / (MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)) + R * t / 3)) ∧
      (t ≤ MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)) / R →
        (d : ℝ) * Real.exp (-(t ^ 2 / 2) / (MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)) + R * t / 3)) ≤
          (d : ℝ) * Real.exp (-3 * t ^ 2 / (8 * MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2))))) ∧
      (MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)) / R ≤ t →
        (d : ℝ) * Real.exp (-(t ^ 2 / 2) / (MatrixTail.Gaussian.specNorm (∑ k, MatrixTail.Master.mean P (fun ω => X k ω ^ 2)) + R * t / 3)) ≤
          (d : ℝ) * Real.exp (-3 * t / (8 * R))) := by sorry

end MatrixTail.Bernstein
