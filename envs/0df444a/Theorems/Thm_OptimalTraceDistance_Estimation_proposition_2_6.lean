-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_proposition_2_6
-- name    : OptimalTraceDistance.Estimation.proposition_2_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:35.902258+00:00
-- url     : https://prove2.me/theorems/1ff63f13-6b70-42a2-b893-a1d8eb829d7f
-- title:
--   Proposition 2.6 — multiscale polynomial bounds
-- statement:
--   There is a universal $C>0$ such that for all $d\ge2$, $0<\varepsilon\le1/32$ and Hermitian $X,Y$ with $X\succeq0$, $\operatorname{tr}X\le1$, $-X\preceq Y\preceq X$, the constructed polynomial satisfies
--   $$\deg F_{d,\varepsilon}\le C\sqrt d/\varepsilon,\qquad |F_{d,\varepsilon}(X,Y)-\operatorname{tr}|Y||\le\varepsilon.$$
--   Every order-$j$ Taylor coefficient, $1\le j\le\deg F$, has an ordered representation with budget
--   $$M_1\le\frac{C\log d}{\varepsilon^3},\qquad M_j\le\frac{(Cd/\varepsilon^2)^j}{d\varepsilon(2j)!}\quad(j\ge2).$$
--   The same universal constant covers the displayed estimates. The pair may be zero or subnormalized.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
--   - encoding: A sufficiently large universal construction constant in (12) → A=2^30; ordered representation budgets use the displayed upper bounds directly; reason: The estimates in (65)-(67) require at most A≥2^21; choosing a larger fixed universal A preserves the source construction and no sample constant is fixed
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Proposition 2.6, p. 9.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem proposition_2_6 : ∃ C : ℝ, 0 < C ∧ ∀ d : ℕ, 2 ≤ d →
  ∀ ε : ℝ, 0 < ε → ε ≤ 1/32 → ∀ X Y : Mat d,
  X.IsHermitian → Y.IsHermitian → X.PosSemidef → tr X ≤ 1 →
  lePSD (-X) Y → lePSD Y X →
    (expressionDegree (F d ε) : ℝ) ≤ C*Real.sqrt d/ε ∧
    |(evaluate (F d ε) X Y).re - QAlgorithms.traceNorm Y| ≤ ε ∧
    ∀ j : ℕ, 1 ≤ j → j ≤ expressionDegree (F d ε) →
      HasOrderedBound j (taylor (F d ε) X Y j)
        (if j = 1 then C*Real.log d/ε^3 else
          (C*d/ε^2)^j / ((d : ℝ)*ε*((2*j).factorial : ℝ))) := by sorry

end OptimalTraceDistance.Estimation
