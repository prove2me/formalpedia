-- Prove2me | Theorems.Thm_HighDimStat_RandomMatrices_matrix_bernstein_bound_v2
-- name    : HighDimStat.RandomMatrices.matrix_bernstein_bound_v2
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-10-06T06:20:28.090715+00:00
-- url     : https://prove2.me/theorems/eda8f5a5-49ae-451e-8b59-8f38257cd21d
-- title:
--   Theorem 6.17 — the matrix Bernstein bound (for $\delta>0$)
-- statement:
--   **Theorem 6.17 (Bernstein bound for random matrices).** Let $\{Q_i\}_{i=1}^n$ be a sequence
--   of independent, zero-mean, symmetric random matrices that satisfy the Bernstein condition
--   (Definition 6.10) with parameter $b>0$. Then for all $\delta>0$, the operator norm
--   satisfies the tail bound
--
--   $$
--   \mathbb P\Big[\frac1n\Big|\!\Big|\!\Big|\sum_{i=1}^n Q_i\Big|\!\Big|\!\Big|_2 \ge \delta\Big] \;\le\;
--   2\,\mathrm{rank}\Big(\sum_{i=1}^n\mathrm{var}(Q_i)\Big)\exp\Big(-\frac{n\delta^2}{2(\sigma^2+b\delta)}\Big),
--   $$
--
--   where $\sigma^2 := \frac1n\big|\!\big|\!\big|\sum_{j=1}^n\mathrm{var}(Q_j)\big|\!\big|\!\big|_2$.
--
--   This is the chapter's central matrix concentration tool, generalizing the scalar Bernstein
--   bound (Chapter 2) to the operator norm of a sum of random matrices; it is the basis of
--   Theorem 6.23's proof.
--
--   **Formalization Note.** The retired version (`matrix_bernstein_bound`) stated the bound for
--   all $\delta\ge0$, as printed. At $\delta=0$ the left side is $\mathbb P[\|\cdot\|\ge0]=1$ while
--   the right side is $2\,\mathrm{rank}(\sum_i\mathrm{var}(Q_i))$, which is $0$ whenever the total
--   variance vanishes (all $Q_i=0$ a.s., e.g. in dimension $d=0$), so the printed inequality reads
--   $1\le0$ there (accepted disproof). This is a degenerate failure of the **printed source**; the
--   corrected statement restricts to $\delta>0$, which loses nothing (for $\delta=0$ and nonzero
--   total variance the bound is the trivial $1\le 2\,\mathrm{rank}$, and for zero total variance
--   the left side is $0$ for every $\delta>0$). The $\mathrm{rank}(\cdot)$ factor is kept exactly
--   (not replaced by the ambient dimension $d$); independence is Mathlib's `iIndepFun` with the
--   local `MeasurableSpace` instance on matrices; zero mean, symmetry and the moment condition are
--   packaged in `BernsteinConditionMatrix`.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 176 (PDF p. 196), Theorem 6.17, Eq. (6.42) — stated for δ > 0; the printed 'for all δ ≥ 0' fails at δ = 0 when the total variance is zero

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_BernsteinConditionMatrix
import Definitions.Def_HighDimStat_RandomMatrices_matrixVariance
import Definitions.Def_HighDimStat_RandomMatrices_opNorm

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices

noncomputable instance instMeasurableSpaceMatrixV2 {d : ℕ} :
    MeasurableSpace (Matrix (Fin d) (Fin d) ℝ) := by
  unfold Matrix; infer_instance

/-- **Theorem 6.17** (Bernstein bound for random matrices), Wainwright, *High-Dimensional
Statistics* (2019), p. 176, Eq. (6.42). Let `{Qᵢ}` be independent, zero-mean, symmetric random
matrices satisfying the Bernstein condition with parameter `b > 0`. Then for all `δ > 0`, the
operator norm satisfies
`P[(1/n)|||∑Qᵢ|||₂ ≥ δ] ≤ 2 rank(∑var(Qᵢ)) exp(-nδ²/(2(σ²+bδ)))`, where
`σ² := (1/n)|||∑var(Qᵢ)|||₂`.

Correction to the printed source: the bound is stated here for `δ > 0` rather than the printed
`δ ≥ 0`. At `δ = 0` the left side is `P[‖·‖ ≥ 0] = 1`, while the right side is
`2·rank(∑var(Qᵢ))`, which vanishes whenever the total variance is zero (all `Qᵢ = 0` a.s., in
particular in dimension `d = 0`); the printed inequality `1 ≤ 0` is false there, and the
`δ = 0` case carries no content otherwise (the bound reads `1 ≤ 2·rank ≥ 2`). For `δ > 0` the
statement is exactly the printed one. -/
theorem matrix_bernstein_bound_v2 {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω] {Prob : Measure Ω}
    [IsProbabilityMeasure Prob] (Q : Fin n → Ω → Matrix (Fin d) (Fin d) ℝ) (b : ℝ) (hb : 0 < b)
    (hIndep : iIndepFun Q Prob)
    (hBernstein : ∀ i, BernsteinConditionMatrix (Q i) Prob b)
    (δ : ℝ) (hδ : 0 < δ) :
    Prob.real {ω | δ ≤ opNorm (∑ i, Q i ω) / (n : ℝ)} ≤
      2 * (Matrix.rank (∑ i, matrixVariance (Q i) Prob) : ℝ) *
        Real.exp (-((n : ℝ) * δ ^ 2) /
          (2 * ((1 / (n : ℝ)) * opNorm (∑ i, matrixVariance (Q i) Prob) + b * δ))) := by sorry

end HighDimStat.RandomMatrices
