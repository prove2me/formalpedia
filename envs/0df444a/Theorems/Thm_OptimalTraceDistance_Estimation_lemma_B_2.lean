-- Prove2me | Theorems.Thm_OptimalTraceDistance_Estimation_lemma_B_2
-- name    : OptimalTraceDistance.Estimation.lemma_B_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-09T05:44:53.547552+00:00
-- url     : https://prove2.me/theorems/eb213d51-eda3-4015-967e-681526e868c5
-- title:
--   Lemma B.2 — filtered polynomial Taylor coefficients
-- statement:
--   Let $0<b\le1$, $K\ge2$ and $2^8b\le s\le2^9b$. Let $X,Y$ be Hermitian with $0\preceq X\preceq I$ and $-X\preceq Y\preceq X$. Expand
--   $$\operatorname{tr}q_{K,s}\!\left(R_b(X+tE_0)(Y+tE_1)R_b(X+tE_0)\right)=\sum_{j\ge0}t^j\Phi_j(E_0,E_1).$$
--   For every $j\ge1$, $\Phi_j$ has an ordered representation valid for all complex matrices $E_0,E_1$, with bound
--   $$2^{10}Kb\,\frac{(2^{16}K^2/b)^j}{(2j)!}.$$
--   There is no trace normalization assumption on $X$. The known representation factors depend on the base pair, never on the perturbations.
--
--   Differences from the source:
--   - encoding: Positive-dimensional complex matrices and source trace expressions → Fin d matrices; retained ordered words; real parts of real traces; explicit finite index sums; reason: Indexing and real extraction preserve all source instances; no rank or commutativity restriction is added
-- source:
--   Ziyun Chen, Minbo Gao, Qisheng Wang, STOC 2027 submission #875 (October 2026), Lemma B.2, p. 29.

import Definitions.Def_OptimalTraceDistance_Estimation_Algorithm2

open MeasureTheory
open scoped BigOperators Matrix Classical ENNReal ComplexOrder
noncomputable section

namespace OptimalTraceDistance.Estimation

theorem lemma_B_2 (d K : ℕ) (hd : 0 < d) (hK : 2 ≤ K)
    (b s : ℝ) (hb : 0 < b) (hb1 : b ≤ 1)
    (hslo : (2 : ℝ)^8*b ≤ s) (hshi : s ≤ (2 : ℝ)^9*b)
    (X Y : Mat d) (hX : X.IsHermitian) (hY : Y.IsHermitian)
    (hX0 : X.PosSemidef) (hXI : lePSD X 1) (hlo : lePSD (-X) Y) (hhi : lePSD Y X) :
  let r := exprPoly (filter b) (exprVar d false)
  let g := traceExpr (exprPoly (qScaled K s) (exprMul (exprMul r (exprVar d true)) r))
  ∀ j : ℕ, 1 ≤ j → HasOrderedBound j (taylor g X Y j)
    ((2 : ℝ)^10*K*b * ((2 : ℝ)^16*(K : ℝ)^2/b)^j / ((2*j).factorial : ℝ)) := by sorry

end OptimalTraceDistance.Estimation
