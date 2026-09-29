-- Prove2me | Theorems.Thm_HighDimStat_RandomMatrices_thresholded_covariance_estimation_bound
-- name    : HighDimStat.RandomMatrices.thresholded_covariance_estimation_bound
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-20T04:23:56.72476+00:00
-- url     : https://prove2.me/theorems/ed972da4-2691-48c5-a9f6-23c650df4e21
-- title:
--   Theorem 6.23 -- thresholding-based covariance estimation
-- statement:
--   **Theorem 6.23 (Thresholding-based covariance estimation).** Let $\{x_i\}_{i=1}^n$ be an
--   i.i.d. sequence of zero-mean random vectors with covariance matrix $\Sigma$, and suppose that
--   each component $x_{ij}$ is sub-Gaussian with parameter at most $\sigma$. If $n>\log d$, then
--   for any $\delta>0$, the thresholded sample covariance matrix $T_{\lambda_n}(\hat\Sigma)$ with
--   $\lambda_n/\sigma^2 = 8\sqrt{\log d/n}+\delta$ satisfies
--
--   $$
--   \mathbb P\big[\,|\!|\!|T_{\lambda_n}(\hat\Sigma)-\Sigma|\!|\!|_2 \ge 2|\!|\!|A|\!|\!|_2\lambda_n\,\big]
--   \;\le\; 8e^{-\frac{n}{16}\min\{\delta,\delta^2\}}.
--   $$
--
--   This is the chapter's title result for structured (sparse) covariance estimation: when the
--   zero pattern of $\Sigma$ is unknown but its adjacency-graph sparsity $|\!|\!|A|\!|\!|_2$ is
--   controlled, simple entrywise thresholding of the sample covariance matrix attains an error
--   that scales with the graph's sparsity rather than the ambient dimension $d$.
--
--   **Formalization Note** "i.i.d. sequence of zero-mean random vectors" is realized as
--   `iIndepFun` (mutual independence) together with `IdentDistrib` of each `x i` against a
--   reference index (identical distribution), plus explicit coordinatewise mean-zero and
--   covariance-$\Sigma$ hypotheses stated at the reference index. "Each component sub-Gaussian
--   with parameter $\sigma$" is restated locally (per this book's cross-chapter reuse rule,
--   rather than importing Chapter 2's `IsSubGaussian` draft) as the explicit MGF bound at the
--   reference index. The adjacency matrix $A$ and thresholding operator $T_{\lambda_n}$ are the
--   definitions above, not simplified or assumed.
-- source:
--   Wainwright, High-Dimensional Statistics, CUP 2019, p. 181 (PDF p. 201), Theorem 6.23, Eq. (6.53)

import Mathlib
import Definitions.Def_HighDimStat_RandomMatrices_thresholdMatrix
import Definitions.Def_HighDimStat_RandomMatrices_adjacencyMatrix
import Definitions.Def_HighDimStat_RandomMatrices_opNorm
import Definitions.Def_HighDimStat_RandomMatrices_sampleCovariance

open MeasureTheory ProbabilityTheory

namespace HighDimStat.RandomMatrices

/-- **Theorem 6.23** (Thresholding-based covariance estimation), Wainwright, *High-Dimensional
Statistics* (2019), p. 181. Let `{xᵢ}` be an i.i.d. sequence of zero-mean random vectors with
covariance matrix `Σ`, and suppose each component `x_{ij}` is sub-Gaussian with parameter at
most `σ`. If `n > log d`, then for any `δ > 0`, the thresholded sample covariance matrix
`Tλn(Σ̂)` with `λn/σ² = 8√(log d/n) + δ` satisfies
`P[|||Tλn(Σ̂)-Σ|||₂ ≥ 2|||A|||₂λn] ≤ 8e^{-(n/16)min{δ,δ²}}`. -/
theorem thresholded_covariance_estimation_bound {n d : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {Prob : Measure Ω} [IsProbabilityMeasure Prob] (x : Fin n → Ω → Fin d → ℝ)
    (Sig : Matrix (Fin d) (Fin d) ℝ) (σ : ℝ) (hn0 : 0 < n)
    (hIndep : iIndepFun x Prob)
    (hIdent : ∀ i, IdentDistrib (x i) (x ⟨0, hn0⟩) Prob Prob)
    (hMean0 : ∀ j, ∫ ω, x ⟨0, hn0⟩ ω j ∂Prob = 0)
    (hCov : ∀ j k, ∫ ω, x ⟨0, hn0⟩ ω j * x ⟨0, hn0⟩ ω k ∂Prob = Sig j k)
    (hSubG : ∀ j, ∀ lam' : ℝ, Integrable (fun ω => Real.exp (lam' * x ⟨0, hn0⟩ ω j)) Prob ∧
      ∫ ω, Real.exp (lam' * x ⟨0, hn0⟩ ω j) ∂Prob ≤ Real.exp (σ ^ 2 * lam' ^ 2 / 2))
    (hnd : Real.log d < n)
    (δ : ℝ) (hδ : 0 < δ) (lam : ℝ)
    (hlam : lam / σ ^ 2 = 8 * Real.sqrt (Real.log d / n) + δ) :
    Prob.real {ω | 2 * opNorm (adjacencyMatrix Sig) * lam ≤
      opNorm (thresholdMatrix lam (sampleCovariance (fun i => x i ω)) - Sig)} ≤
      8 * Real.exp (-((n : ℝ) / 16) * min δ (δ ^ 2)) := by sorry

end HighDimStat.RandomMatrices
