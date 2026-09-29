-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_summable_rho
-- name    : MarkovChainCLT.clt_of_summable_rho
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:41:29.378603+00:00
-- url     : https://prove2.me/theorems/fc19ced7-4d79-44ef-b56a-b70369f3c9a1
-- title:
--   $\rho$-mixing CLT: $E Y^2 < \infty$, $\sum \rho(n) < \infty$ (Jones Thm 7)
-- statement:
--   Let $Y = \{Y_n\}_{n \ge 0}$ be a centered, strictly stationary sequence of real random variables on a probability space, with partial sums $S_n = \sum_{i < n} Y_i$. Suppose $E[Y_0^2] < \infty$ and the $\rho$-mixing coefficients are summable,
--
--   $$
--   \sum_{n} \rho(n) \;<\; \infty.
--   $$
--
--   Then the series
--
--   $$
--   \sigma^2 \;=\; E[Y_0^2] \;+\; 2 \sum_{k \ge 1} E[Y_0 Y_k]
--   $$
--
--   converges absolutely, and if $\sigma^2 > 0$ then $S_n / \sqrt{n} \xrightarrow{d} N(0, \sigma^2)$ as $n \to \infty$.
--
--   For $\rho$-mixing sequences (Ibragimov 1975; the source's eq. (12)) a bare second moment suffices for the CLT — the key to the reversible-chain corollary.
--
--   **Formalization Note** Sequences are indexed from $0$, so $S_n = Y_0 + \cdots + Y_{n-1}$ and the past $\sigma$-algebras used by the mixing coefficients start at $Y_0$; under strict stationarity this agrees with the source, which indexes from $1$. Absolute convergence of the covariance series is expressed as unconditional summability, and the limit statement is weak convergence of the laws of $S_n/\sqrt{n}$.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 7, eq. (12) (arXiv v2 p. 12); original: I. A. Ibragimov, A note on the central limit theorem for dependent random variables, Theory Probab. Appl. 20 (1975)

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 7** (Ibragimov 1975): a centered strictly stationary
square-integrable ρ-mixing sequence with `∑_n ρ(n) < ∞` satisfies
`σ² = E[Y₀²] + 2 ∑_{k≥1} E[Y₀ Y_k]` (absolutely convergent), and if `σ² > 0` then
`S_n / √n →d N(0, σ²)`. -/

theorem MarkovChainCLT.clt_of_summable_rho {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hρ : Summable (fun n => rhoMixingCoef P Y n)) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by sorry
