-- Prove2me | Theorems.Thm_KingmanSubadditive_PositiveMatrices_theorem_5
-- name    : KingmanSubadditive.PositiveMatrices.theorem_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:16:59.21515+00:00
-- url     : https://prove2.me/theorems/cd20016d-9402-4a77-875f-7593f586296e
-- title:
--   Theorem 5 (Furstenberg–Kesten) — n⁻¹ log [Y₁⋯Y_n]_ij converges with probability one and in mean to a finite λ independent of i, j
-- statement:
--   Let $Y_1,Y_2,\dots$ be random $k\times k$ matrices ($k\ge1$) on a probability space, and let
--   $$X_n=Y_1Y_2\cdots Y_n .$$
--   Suppose that
--   1. the elements of the matrices $Y_n$ are strictly positive;
--   2. their logarithms have finite expectations: $E|\log [Y_n]_{ij}|<\infty$ for all $n\ge1$ and all $i,j$;
--   3. the sequence $(Y_n)$ is stationary (its joint law is invariant under the shift $n\mapsto n+1$).
--
--   Then there is a single finite random variable $\lambda$ with $E|\lambda|<\infty$ such that for every $(i,j)$ the limit
--   $$\lambda=\lim_{n\to\infty} n^{-1}\log [X_n]_{ij}\qquad(2.2.2)$$
--   exists with probability one and in mean ($E|n^{-1}\log [X_n]_{ij}-\lambda|\to0$); in particular it does not depend on $i$ or $j$.
--
--   This is (a variant of) the Furstenberg–Kesten theorem on products of random matrices; Kingman derives it as a corollary of his subadditive ergodic theorem. The quantity $\lambda$ is the top Lyapunov exponent of the product.
--
--   **Formalization Note.** One random variable serves every entry. The logarithm is applied only to strictly positive numbers because positivity of the $Y_n$ is a hypothesis; the paper's index $1$ is `0 : Fin k`.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 891, Theorem 5

import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology

namespace KingmanSubadditive.PositiveMatrices

/-- **Theorem 5** (Furstenberg–Kesten), p. 891 (Kingman, *Subadditive ergodic theory*, Ann.
Probab. 1(6):883–899 (1973)). Suppose that the elements of the random `k × k` matrices `Y_n` are
strictly positive, that their logarithms have finite expectations, and that the sequence
`(Y_n)` is stationary. Then the finite limit `λ = lim_{n→∞} n⁻¹ log [X_n]_ij`, (2.2.2), with
`X_n = Y₁ Y₂ ⋯ Y_n`, exists with probability one and in mean, and does not depend on `i` or `j`.

**Formalization Note.** One random variable `lam` (`λ` is a Lean keyword) serves every
`(i, j)`: that is "does not depend on i or j". "Finite" is `lam : Ω → ℝ`; "in mean" is
`E|n⁻¹ log [X_n]_ij − λ| → 0` with `λ` integrable. `Real.log` is the genuine logarithm because
every entry of `X_n`, `n ≥ 1`, is strictly positive. Stationarity is joint-law stationarity of
`(Y_n)_{n≥1}`, positivity holds for every outcome, `k ≥ 1`. -/
theorem theorem_5 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    ∃ lam : Ω → ℝ, Integrable lam P ∧ ∀ i j : Fin k,
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Real.log (X Y n ω i j) / n) atTop (𝓝 (lam ω))) ∧
      Tendsto (fun n : ℕ => ∫ ω, |Real.log (X Y n ω i j) / n - lam ω| ∂P) atTop (𝓝 0) := by sorry

end KingmanSubadditive.PositiveMatrices
