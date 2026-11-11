-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_negative_core_transfer
-- name    : IndependentInfoPricing.Main.negative_core_transfer
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:42.356147+00:00
-- url     : https://prove2.me/theorems/cf5c8875-c027-4bc0-9acf-3165a20cfe6a
-- title:
--   Lemma 4.26 — Transfer of the negative core
-- statement:
--   Under the occurring-branch half-tail property and finite attained branch monopoly prices, suppose $\lambda=\sum_{j:b_j>0}\beta_j>4$. There exists a threshold $t>0$ satisfying both
--
--   $$\sum_j\beta_j\mathbb E\min(D_j^-,t)=4t,\qquad\mathbb E\varphi_-\le35R.$$
--
--   Here $\varphi_-(\xi)=\min(\bar a(\xi),U_-(\xi))$ uses the truncated core, not the capped values in the mean equation. Threshold existence is part of the conclusion. This lemma handles the large-$\lambda$ regime; it is not an extra assumption in the headline approximation theorem.
--
--   Differences from the source:
--   - generalization: continuously differentiable marginal densities in the upper-bound section → probability marginals with no atom at zero and finite monopoly-price attainment on occurring branches; reason: these intermediate arguments use product laws and branch revenues without differentiability; every source instance satisfies these hypotheses
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.26, printed pp.50–50 (PDF pp.52–52); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Analysis

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 4.26, pp.50–53 (PDF 52–55), including threshold existence. -/
theorem negative_core_transfer {Q : ℕ} (F : Marginals (Fin Q))
    (hF : BranchScope F) (hhalf : BranchHalfTail F) (hLambda : 4 < lambda F) :
    ∃ t : ℝ, 0 < t ∧ negativeCappedMean F t = ENNReal.ofReal (4 * t) ∧
      signExpectation F (phiMinus F t) ≤ 35 * benchmark (productLaw F) := by sorry

end IndependentInfoPricing.Main
