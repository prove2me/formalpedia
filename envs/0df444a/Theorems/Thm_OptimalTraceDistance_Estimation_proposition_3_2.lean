-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_proposition_3_2
-- name    : OptimalTraceDistance.Estimation.proposition_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:45:00.33245+00:00
-- url     : https://prove2.me/theorems/ca012cdf-ccb9-447a-bd24-ef296fdf7e88
-- title:
--   Proposition 3.2 — degree and variance bound
-- statement:
--   There are universal $d_0\ge2$ and $C>0$ such that for $d\ge d_0$, $0<\varepsilon\le1/32$, arbitrary density pairs and every orthogonal projector $Q$, every integer
--   $$n\ge\frac{Cd^2}{\varepsilon^2\log^2d\max\{1,\varepsilon^2\log^2d\}}$$
--   satisfies $n\ge\deg f$, where $f$ is the complete expression (27). If additionally $\|QS_+Q\|_\infty\le1/\log d$, then
--   $$\operatorname{Var}\widehat f_n\le\varepsilon^2/64.$$
--   The norm condition is only on the variance conclusion. It is not needed for degree legality.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
--   - encoding: f in (27) with sufficiently large universal construction constants → C0=2^40 and A=2^30; sample constant C and threshold d0 remain existential; reason: Construction choices are fixed uniformly; the unknown sample-rate constant is not assigned a numerical value
--   - encoding: Subset-normalized U-statistics of symmetric word kernels → Average over all ordered injective register embeddings; a trailing word coefficient is moved to the first factor by trace cyclicity; reason: Each k-subset occurs k! times in the embedding average, cancelling the identical normalization factor; word traces and symmetric kernels are unchanged
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Proposition 3.2, p. 12.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem proposition_3_2 : ∃ d₀ : ℕ, 2 ≤ d₀ ∧ ∃ C : ℝ, 0 < C ∧
  ∀ d : ℕ, d₀ ≤ d → ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 →
  ∀ ρ σ : Mat d, Density ρ → Density σ → ∀ Q : Mat d, projector Q →
  ∀ n : ℕ, C*rate d ε ≤ (n : ℝ) →
    expressionDegree (f d ε Q) ≤ n ∧
    (opNorm (compress Q (plus ρ σ)) ≤ 1/Real.log d →
      polynomialVariance (f d ε Q) n ρ σ ≤ ε^2/64) := by sorry

end OptimalTraceDistance.Estimation
