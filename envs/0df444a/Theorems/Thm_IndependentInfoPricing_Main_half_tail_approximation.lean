-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_half_tail_approximation
-- name    : IndependentInfoPricing.Main.half_tail_approximation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:12.005529+00:00
-- url     : https://prove2.me/theorems/11f12ab5-7095-4b98-9407-7e4c73f2d93e
-- title:
--   Theorem 4.19 — Half-tail approximation
-- statement:
--   For every positive finite number $Q$ of states, let the normalized signed payoff coordinates be independent real random variables. Assume each marginal has a Lebesgue density continuously differentiable on the interior of its support. Every positive-probability positive or negative magnitude branch must have a monopoly-revenue supremum attained at a finite nonnegative price and obey $\Pr(D\ge\operatorname{Rev}(D))\ge1/2$. Then
--
--   $$\operatorname{OPT}\le1094\widetilde R.$$
--
--   The constant is uniform over $Q$, the sign probabilities and the magnitude laws. The scope includes unbounded supports and infinite first moments; interval support, regularity, fixed signs and strictly positive sign probabilities are not assumed. Both free outside options and every response rule remain in the optimum. This is the positive clause of the main theorem.
--
--   Differences from the source:
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Theorem 4.19, printed pp.43–43 (PDF pp.45–45); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Laws

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Theorem 4.19, p.43 (PDF 45), with exactly 1094 and all marginal laws in §4.1's scope. -/
theorem half_tail_approximation {Q : ℕ} (hQ : 0 < Q) (F : Marginals (Fin Q))
    (hF : HalfTailScope F) :
    opt (productLaw F) ≤ 1094 * benchmarkSym (productLaw F) := by sorry

end IndependentInfoPricing.Main
