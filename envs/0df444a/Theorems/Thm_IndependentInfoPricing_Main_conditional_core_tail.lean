-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_conditional_core_tail
-- name    : IndependentInfoPricing.Main.conditional_core_tail
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:01.387759+00:00
-- url     : https://prove2.me/theorems/5f650853-3d03-47b9-ab5a-02e02d6e8441
-- title:
--   Proposition 4.20 — Conditional core–tail
-- statement:
--   Let $W_1,\ldots,W_d$ be independent nonnegative real random variables with arbitrary probability laws, and let $t>0$. Put $a_i=\operatorname{Rev}(W_i)$ and $\mu_i(t)=\mathbb E[W_i1_{W_i\le t}]$. Then
--
--   $$\operatorname{BRev}(W)\le\operatorname{OPT}^{\rm cl}(W)\le\sum_i\mu_i(t)+\left(1+\sum_i\Pr(W_i>t)\right)\sum_i a_i.$$
--
--   The classical optimum is computed from additive IC, nonnegative prices and IR0 only. No regularity, finite support, finite first moment or finite-revenue hypothesis is imposed; the extended quantities retain the displayed inequality when a revenue is infinite. The empty block is included. This is the core–tail estimate used separately on the two conditional magnitude blocks.
--
--   Differences from the source:
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Proposition 4.20, printed pp.45–45 (PDF pp.47–47); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Laws

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Proposition 4.20, p.45 (PDF 47), (74); arbitrary nonnegative real laws. -/
theorem conditional_core_tail {d : ℕ} (W : Marginals (Fin d)) (hW : nonnegativeLaws W)
    (t : ℝ) (ht : 0 < t) :
    bundleRevenue W ≤ optClassical (productLaw W) ∧
    optClassical (productLaw W) ≤
      (∑ i, coreMean (W i) t) + (1 + ∑ i, tailProbability (W i) t) * ∑ i, scalarRevenue (W i) := by sorry

end IndependentInfoPricing.Main
