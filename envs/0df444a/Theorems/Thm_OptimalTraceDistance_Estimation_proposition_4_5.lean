-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_proposition_4_5
-- name    : OptimalTraceDistance.Estimation.proposition_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:45:13.329207+00:00
-- url     : https://prove2.me/theorems/27daa875-1e4c-4b70-9d29-b2d4062b03bb
-- title:
--   Proposition 4.5 — multiscale variance
-- statement:
--   There is a universal $C>0$ such that for every $d\ge2$, $0<\varepsilon\le1/32$, density pair, orthogonal projector $Q$, and $\beta>0$ with $\|QS_+Q\|_\infty\le\beta$, writing $D=\deg F_{d,\varepsilon}$, every $n\ge2D$ satisfies
--   $$\operatorname{Var}G_{F_{d,\varepsilon},Q,n}\le\frac{C\log^2d}{\varepsilon^6n}+\frac{C}{d^2\varepsilon^2}\left[\exp\!\left(\frac{C\sqrt d}{\varepsilon n^{1/4}}\right)+\exp\!\left(C\left(\frac{\beta d^2}{\varepsilon^4n}\right)^{1/3}\right)\right].$$
--   All terms refer to the same compressed multiscale observable, with variance in the normalized labelled state.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
--   - encoding: The fixed multiscale construction with a sufficiently large universal constant → A=2^30 and real powers 1/4,1/3; reason: The source estimates hold for this fixed choice; real powers preserve the printed exponents on their nonnegative domain
--   - encoding: Subset-normalized U-statistics of symmetric word kernels → Average over all ordered injective register embeddings; a trailing word coefficient is moved to the first factor by trace cyclicity; reason: Each k-subset occurs k! times in the embedding average, cancelling the identical normalization factor; word traces and symmetric kernels are unchanged
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Proposition 4.5, p. 20.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem proposition_4_5 : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
  ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 → ∀ ρ σ : Mat d, Density ρ → Density σ →
  ∀ Q : Mat d, projector Q → ∀ β : ℝ, 0 < β → opNorm (compress Q (plus ρ σ)) ≤ β →
  ∀ n : ℕ, 2*expressionDegree (F d ε) ≤ n →
    polynomialVariance (substituteCompression Q (F d ε)) n ρ σ ≤
      C*(Real.log d)^2/(ε^6*n) + C/((d : ℝ)^2*ε^2) *
        (Real.exp (C*Real.sqrt d/(ε*(n : ℝ)^(1/4 : ℝ))) +
          Real.exp (C*(β*(d : ℝ)^2/(ε^4*n))^(1/3 : ℝ))) := by sorry

end OptimalTraceDistance.Estimation
