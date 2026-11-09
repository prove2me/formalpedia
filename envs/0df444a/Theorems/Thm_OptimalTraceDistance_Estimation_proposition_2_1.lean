-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_proposition_2_1
-- name    : OptimalTraceDistance.Estimation.proposition_2_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:07.902274+00:00
-- url     : https://prove2.me/theorems/a023476f-2d43-4c8b-b0ca-5fcd20351fcf
-- title:
--   Proposition 2.1 — order, compression and Schatten bounds
-- statement:
--   For density matrices $\rho,\sigma$ on $\mathbb C^d$, set $S_\pm=(\rho\pm\sigma)/2$. Then
--   $$S_+\succeq0,\quad\operatorname{tr}S_+=1,\quad-S_+\preceq S_-\preceq S_+,\quad\|S_-\|_\infty\le\tfrac12.$$
--   Every orthogonal projector $Q$ gives $QS_+Q\succeq0$, $-QS_+Q\preceq QS_-Q\preceq QS_+Q$, and $\operatorname{tr}(QS_+Q)\le1$.
--
--   For any dominated Hermitian pair $X\succeq0$, $-X\preceq Y\preceq X$, there is a Hermitian $J$ with
--   $$Y=X^{1/2}JX^{1/2},\qquad\|J\|_\infty\le1,\qquad\|Y\|_p\le\|X\|_p\quad(1\le p\le\infty).$$
--   Singular $X$ is allowed. These bounds also apply to subnormalized compressions.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Proposition 2.1, p. 6.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem proposition_2_1 (d : ℕ) (hd : 0 < d) :
  (∀ ρ σ : Mat d, Density ρ → Density σ →
    (plus ρ σ).PosSemidef ∧ (plus ρ σ).trace = 1 ∧
    lePSD (-(plus ρ σ)) (minus ρ σ) ∧ lePSD (minus ρ σ) (plus ρ σ) ∧
    opNorm (minus ρ σ) ≤ 1/2 ∧
    ∀ Q, projector Q → (compress Q (plus ρ σ)).PosSemidef ∧
      lePSD (-(compress Q (plus ρ σ))) (compress Q (minus ρ σ)) ∧
      lePSD (compress Q (minus ρ σ)) (compress Q (plus ρ σ)) ∧
      tr (compress Q (plus ρ σ)) ≤ 1) ∧
  (∀ X Y : Mat d, X.IsHermitian → Y.IsHermitian → X.PosSemidef →
    lePSD (-X) Y → lePSD Y X →
    (∃ J : Mat d, J.IsHermitian ∧ Y = sqrtMat X * J * sqrtMat X ∧ opNorm J ≤ 1) ∧
    ∀ p : ℝ≥0∞, 1 ≤ p → WHMultiplicativity.schattenNorm p Y ≤
      WHMultiplicativity.schattenNorm p X) := by sorry

end OptimalTraceDistance.Estimation
