-- Prove2me | Theorems.Thm_MemOracleLB_Optimization_lemma_2_4
-- name    : MemOracleLB.Optimization.lemma_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-08T10:34:57.429599+00:00
-- url     : https://prove2.me/theorems/f913ac71-748c-43a1-bee4-847ce94199b9
-- title:
--   Lemma 2.4 — Restricted Gaussian is logconcave with Cov ⪯ I/n
-- statement:
--   Let $n>0$ and let $F\subseteq E_n$ be convex with $\bar\gamma_n(F)>0$, where $\bar\gamma_n=N(0,I_n/n)$. For the conditioned law $\mu=\bar\gamma_n(\cdot\mid F)$, all three conclusions hold:
--
--   $$\mu\ll\mathrm{Leb}_n,\qquad \mu\text{ has a log-concave density},\qquad \operatorname{Cov}(\mu)\preceq I_n/n.$$
--
--   The covariance conclusion includes finite second moments and asserts $\operatorname{Var}_\mu\langle w,X\rangle\le\|w\|^2/n$ for every $w$. No Borel or closedness condition is imposed on $F$. This supplies the row laws on positive-measure convex product parts.
--
--   Differences from the source:
--   - encoding: real Euclidean spaces, independent rows and Gaussian relative entropy → EuclideanSpace with Fin indices, product measures and Mathlib klDiv in [0,infinity]; reason: the same spaces, independent laws and divergence values, including infinite entropy
--   - generalization: the sufficiently large ambient dimension convention of §2 → every positive dimension; reason: convex Gaussian restriction has these properties for all n>0, so the source range is included
--   - encoding: the covariance matrix exists and is bounded → finite second moment together with every directional variance bound; reason: the moment condition prevents the default zero value of a nonintegrable variance from satisfying the assertion
-- source:
--   Santosh Vempala, STOC 2027 submission #365 (October 2026), Lemma 2.4, PDF p. 9 (printed p. 8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/365.pdf

import Mathlib
import Definitions.Def_MemOracleLB_Optimization_Probability

open MeasureTheory ProbabilityTheory
open scoped ENNReal RealInnerProductSpace

namespace MemOracleLB.Optimization

/-- Lemma 2.4, PDF p.9 (printed p.8). Convex F need only be Lebesgue null-measurable. -/
theorem lemma_2_4 (n : ℕ) (hn : 0 < n) (F : Set (E n))
    (hF : Convex ℝ F) (hp : 0 < scaledGaussian n F) :
    HasDensity (cond (scaledGaussian n) F) ∧
    LogConcaveLaw (cond (scaledGaussian n) F) ∧
    CovarianceBound (cond (scaledGaussian n) F) (1 / n) := by sorry

end MemOracleLB.Optimization
