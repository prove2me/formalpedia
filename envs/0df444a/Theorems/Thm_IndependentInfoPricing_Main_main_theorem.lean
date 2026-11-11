-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_main_theorem
-- name    : IndependentInfoPricing.Main.main_theorem
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:21.819207+00:00
-- url     : https://prove2.me/theorems/e64ea07c-e56e-4c1d-8e99-9e9a589ce403
-- title:
--   Theorem 1.1 — Main theorem, both clauses
-- statement:
--   The information-pricing problem has both of the following properties.
--
--   1. For every real $K>0$ there is an instance with two independent signed payoff coordinates such that
--
--   $$\operatorname{OPT}>K\widetilde R.$$
--
--   The witness is permitted to be discrete: it is represented by independent finitely supported strictly positive $X,Y$ and $v=(X,-Y)$, as constructed in Theorem 3.1. This clause imposes no density or half-tail restriction.
--
--   2. For every positive finite number $Q$ of coordinates, let the normalized payoff law be the product of arbitrary real probability marginals. Suppose each marginal has a Lebesgue density continuously differentiable on the interior of its support. Suppose every occurring positive and negative magnitude branch has a finite attained monopoly price and satisfies $\Pr(D\ge\operatorname{Rev}(D))\ge1/2$. Then
--
--   $$\operatorname{OPT}\le1094\widetilde R.$$
--
--   Here $\widetilde R$ is the better of actual symmetrized separate selling and priced full revelation. Price vectors are chosen before the buyer's private signs or values are seen. The optimum allows infinitely many reports and full IC against all four response rules with both free outside options. The bound is uniform over the dimension and the sign probabilities, and imposes no finite first moment, bounded support, regularity or fixed-sign assumption. These two clauses express the source's separation and approximation contrast in a single goal.
--
--   Differences from the source:
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Theorem 1.1, printed p.2 (PDF p.4), §§2–3 and 4.5; https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Diagonal

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Theorem 1.1, p.2 (PDF 4), both numbered clauses. The lower clause has no density restriction. -/
theorem main_theorem :
    (∀ K : ℝ, 0 < K → ∃ X Y : Measure ℝ,
      PositiveFiniteLaw X ∧ PositiveFiniteLaw Y ∧
      ENNReal.ofReal K * benchmarkSym (productLaw (oppositeLaw X Y)) < opt (productLaw (oppositeLaw X Y))) ∧
    (∀ Q : ℕ, 0 < Q → ∀ F : Marginals (Fin Q), HalfTailScope F →
      opt (productLaw F) ≤ 1094 * benchmarkSym (productLaw F)) := by sorry

end IndependentInfoPricing.Main
