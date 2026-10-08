-- Prove2me | Theorems.Thm_OAI_PiExponent_DeterminantContradiction_actual_truncated_log_entry_low_index_exp_bound
-- name    : OAI.PiExponent.DeterminantContradiction.actual_truncated_log_entry_low_index_exp_bound
-- status  : Open
-- author  : @Eyal1990
-- created : 2026-10-07T21:39:00.492222+00:00
-- url     : https://prove2.me/theorems/aa1f9e5b-ad85-494d-a859-5b0ff5a5e36b
-- title:
--   Low-index coefficient estimate for truncated-log interpolation matrices
-- statement:
--   Fix an admissible parameter $\nu\ge0$, fixed data $d$, and height $H>0$. Let $M_{d,H}$ be the explicitly defined truncated-log interpolation matrix, with its rows and columns indexed by the corresponding weighted simplices. Then every entry satisfies
--
--   $$
--   \|M_{d,H}[\rho,c]\|\le \exp\!\left(H\left( d.\mathrm{analyticError}+\mathrm{analyticRemainder}(d,H)-\nu\big(A(1-\eta)-\mathrm{actualMean}(d,H)\big)-\frac{\log(\mathrm{actualRowCount}(d,H))}{H}\right)\right).
--   $$
--
--   This coefficient-level estimate is the analytic input used to bound sums of entries in selected minors of the fixed determinant family.
-- source:
--   Analytic coefficient sublemma for the fixed determinant family in the irrationality-exponent proof; see https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/OAI/NumberTheory/PiExponent/Approximation/DeterminantContradiction.lean

import Definitions.Def_OAI_PiExponent_AnalyticRemainder
open OAI.PiExponent OAI.PiExponent.DeterminantContradiction

theorem OAI.PiExponent.DeterminantContradiction.actual_truncated_log_entry_low_index_exp_bound
    {nu : Real} (d : FixedData nu) (hnu : 0 <= nu)
    {H : Real} (hH : 0 < H)
    (rowIdx : Row d H) (colIdx : Column d H) :
    norm ((InterpolationMatrix.truncatedLogMatrix d.K d.w0 d.v0 d.base.theta
      (MatrixArithmetic.logWeights (finiteDenominators d)) H
      (MatrixArithmetic.rationalCenters (finiteNumerators d) (finiteDenominators d))
      (MatrixArithmetic.truncationOrders (finiteDenominators d) d.F0 d.v0)) rowIdx colIdx) <=
      Real.exp (H * (d.analyticError + analyticRemainder d H +
        -nu * ((d.base.A : Real) * (1 - d.base.eta) - actualMean d H) -
        Real.log (actualRowCount d H : Real) / H)) := by sorry
