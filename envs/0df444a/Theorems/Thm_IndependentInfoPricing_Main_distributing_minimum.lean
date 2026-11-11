-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_distributing_minimum
-- name    : IndependentInfoPricing.Main.distributing_minimum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:17.556499+00:00
-- url     : https://prove2.me/theorems/4b481d68-733b-4082-bca4-1295d1be5d2f
-- title:
--   Lemma 4.21 — Distributing the minimum
-- statement:
--   For an occurring sign pattern, use the actual conditional optima, branch revenue sums and core–tail quantities at positive thresholds $\Theta,t$. Write $\varphi=\min(\bar a,\bar b)$ and $\varphi_-=\min(\bar a,U_-)$. Then
--
--   $$\min(C_+,C_-)\le U_+ +(1+A)\varphi_- +(1+A)(1+B)\varphi.$$
--
--   All quantities are defined from the product payoff law; the core–tail estimates are not hidden assumptions of the model. This pointwise inequality connects the conditional classical selling problems to the weighted sign expectations.
--
--   Differences from the source:
--   - generalization: continuously differentiable marginal densities in the upper-bound section → probability marginals with no atom at zero and finite monopoly-price attainment on occurring branches; reason: these intermediate arguments use product laws and branch revenues without differentiability; every source instance satisfies these hypotheses
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.21, printed pp.46–46 (PDF pp.48–48); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Analysis

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 4.21, p.46 (PDF 48), (77), using actual conditional quantities. -/
theorem distributing_minimum {Q : ℕ} (F : Marginals (Fin Q)) (hF : BranchScope F)
    (Θ t : ℝ) (hΘ : 0 < Θ) (ht : 0 < t) (S : Finset (Fin Q)) (hS : signWeight F S ≠ 0) :
    min (positiveClassical F S) (negativeClassical F S) ≤
      uPlus F Θ S + (1 + tailsPlus F Θ S) * phiMinus F t S +
      (1 + tailsPlus F Θ S) * (1 + tailsMinus F t S) * phi F S := by sorry

end IndependentInfoPricing.Main
