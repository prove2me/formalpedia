-- Prove2me | Theorems.Thm_KingmanSubadditive_PositiveMatrices_limit_11
-- name    : KingmanSubadditive.PositiveMatrices.limit_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:17:42.047692+00:00
-- url     : https://prove2.me/theorems/282d3869-e19c-435b-bd7e-8dce16061967
-- title:
--   Proof of Theorem 5, p. 892 — the limit (2.2.2) exists when i = j = 1
-- statement:
--   Assume the hypotheses of Theorem 5 and let $X_n=Y_1Y_2\cdots Y_n$. Then there is a finite random variable $\lambda$ with $E|\lambda|<\infty$ such that
--   $$\lambda=\lim_{n\to\infty} n^{-1}\log [X_n]_{11}$$
--   with probability one and in mean, i.e. also $E\,|n^{-1}\log [X_n]_{11}-\lambda|\to0$.
--
--   This is the diagonal case of (2.2.2); in the paper it is obtained by applying Theorem 1 to $x_{st}=-\log[Y_{s+1}\cdots Y_t]_{11}$.
-- source:
--   Kingman, Subadditive ergodic theory, Ann. Probab. 1(6):883–899 (1973), DOI 10.1214/aop/1176996798, p. 892, §2.2, proof of Theorem 5

import Mathlib
import Definitions.Def_KingmanSubadditive_PositiveMatrices_Model
open MeasureTheory Filter Topology

namespace KingmanSubadditive.PositiveMatrices

/-- Proof of Theorem 5, p. 892 (Kingman, *Subadditive ergodic theory*, Ann. Probab.
1(6):883–899 (1973)), unnumbered: "Theorem 1 may therefore be applied to x to show that the
limit (2.2.2) exists when i = j = 1." Under the hypotheses of Theorem 5 there is a finite,
integrable random variable `λ` with `n⁻¹ log [X_n]₁₁ → λ` with probability one and in mean.

**Formalization Note.** `X_n = Y₁ ⋯ Y_n` (left to right); the paper's index `1` is
`0 : Fin k`. `Real.log` is the genuine logarithm here because every entry of `X_n` (`n ≥ 1`) is
strictly positive under the hypotheses. The `n = 0` term (division by zero) does not affect a
limit. `λ` is a Lean keyword, so the limit is called `lam`. -/
theorem limit_11 {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {k : ℕ} [NeZero k] (Y : ℕ → Ω → Matrix (Fin k) (Fin k) ℝ) (hY : Hypotheses P Y) :
    ∃ lam : Ω → ℝ, Integrable lam P ∧
      (∀ᵐ ω ∂P, Tendsto (fun n : ℕ => Real.log (X Y n ω 0 0) / n) atTop (𝓝 (lam ω))) ∧
      Tendsto (fun n : ℕ => ∫ ω, |Real.log (X Y n ω 0 0) / n - lam ω| ∂P) atTop (𝓝 0) := by sorry

end KingmanSubadditive.PositiveMatrices
