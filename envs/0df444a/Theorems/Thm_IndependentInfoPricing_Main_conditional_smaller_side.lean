-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_conditional_smaller_side
-- name    : IndependentInfoPricing.Main.conditional_smaller_side
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:26.608592+00:00
-- url     : https://prove2.me/theorems/42db13b9-d4d4-4696-9fb0-f80afb0d4bac
-- title:
--   Lemma 4.25 — Smaller-side transfer: conditional form
-- statement:
--   For independent signed payoff coordinates with finite attained monopoly prices on all occurring magnitude branches, assume the half-tail property on those branches. Then
--
--   $$\mathbb E_\xi\min\{\bar a(\xi),\bar b(\xi)\}\le16R.$$
--
--   The sign probabilities may be zero or one. Absent branches have weight zero and carry no shape assumption. The revenue benchmark is the supremum over fixed ex ante activation and deactivation price vectors, together with full revelation; conditional optima or sign-dependent price vectors do not replace it. This is the smaller-side estimate required by the abstract bound.
--
--   Differences from the source:
--   - generalization: continuously differentiable marginal densities in the upper-bound section → probability marginals with no atom at zero and finite monopoly-price attainment on occurring branches; reason: these intermediate arguments use product laws and branch revenues without differentiability; every source instance satisfies these hypotheses
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.25, printed pp.49–49 (PDF pp.51–51); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Analysis

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 4.25, pp.49–50 (PDF 51–52), (87); prices cannot depend on signs. -/
theorem conditional_smaller_side {Q : ℕ} (F : Marginals (Fin Q))
    (hF : BranchScope F) (hhalf : BranchHalfTail F) :
    signExpectation F (phi F) ≤ 16 * benchmark (productLaw F) := by sorry

end IndependentInfoPricing.Main
