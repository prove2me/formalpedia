-- Prove2me | Theorems.Thm_MarkovChainCLT_clt_of_summable_sqrt_phi
-- name    : MarkovChainCLT.clt_of_summable_sqrt_phi
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-08-15T14:42:11.371368+00:00
-- url     : https://prove2.me/theorems/79efa991-ad71-4fb9-8e30-adde6a5eb4e9
-- title:
--   $\varphi$-mixing CLT: $E Y^2 < \infty$, $\sum \sqrt{\varphi(n)} < \infty$ (Jones Thm 8)
-- statement:
--   Let $Y = \{Y_n\}_{n \ge 0}$ be a centered, strictly stationary sequence of real random variables on a probability space, with partial sums $S_n = \sum_{i < n} Y_i$. Suppose $E[Y_0^2] < \infty$ and the uniform mixing coefficients satisfy
--
--   $$
--   \sum_{n} \sqrt{\varphi(n)} \;<\; \infty.
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
--   The classical uniformly mixing CLT (Billingsley; Ibragimov–Linnik; the source's eq. (13)), the engine behind the uniformly ergodic chain CLT.
--
--   **Formalization Note** Sequences are indexed from $0$, so $S_n = Y_0 + \cdots + Y_{n-1}$ and the past $\sigma$-algebras used by the mixing coefficients start at $Y_0$; under strict stationarity this agrees with the source, which indexes from $1$. Absolute convergence of the covariance series is expressed as unconditional summability, and the limit statement is weak convergence of the laws of $S_n/\sqrt{n}$.
-- source:
--   G. L. Jones, "On the Markov Chain Central Limit Theorem", Probability Surveys 1 (2004) 299-320, arXiv math/0409112v2, Theorem 8, eq. (13) (arXiv v2 p. 12); originals: P. Billingsley, Convergence of Probability Measures (1968), Theorem 20.1; Ibragimov & Linnik (1971)

import Definitions.Def_MixingCoefficients
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Topology ProbabilityTheory

/-- **Theorem 8** (Billingsley 1968; Ibragimov–Linnik 1971): a centered strictly
stationary square-integrable uniformly mixing sequence with `∑_n √φ(n) < ∞`
satisfies `σ² = E[Y₀²] + 2 ∑_{k≥1} E[Y₀ Y_k]` (absolutely convergent), and if
`σ² > 0` then `S_n / √n →d N(0, σ²)`. -/

theorem MarkovChainCLT.clt_of_summable_sqrt_phi {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (Y : ℕ → Ω → ℝ)
    (hY : ∀ n, Measurable (Y n)) (hstat : IsStrictlyStationary P Y)
    (hcent : ∫ ω, Y 0 ω ∂P = 0) (hL2 : MemLp (Y 0) 2 P)
    (hφ : Summable (fun n => Real.sqrt (phiMixingCoef P Y n))) :
    Summable (fun k : ℕ => ∫ ω, Y 0 ω * Y (k + 1) ω ∂P) ∧
      (0 < seqAsymptoticVariance P Y →
        TendstoInDistribution
          (fun (n : ℕ) ω => (Real.sqrt n)⁻¹ * ∑ i ∈ Finset.range n, Y i ω)
          atTop (id : ℝ → ℝ) (fun _ => P)
          (gaussianReal 0 (seqAsymptoticVariance P Y).toNNReal)) := by sorry
