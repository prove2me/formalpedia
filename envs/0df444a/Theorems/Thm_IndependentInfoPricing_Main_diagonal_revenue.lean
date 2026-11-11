-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_diagonal_revenue
-- name    : IndependentInfoPricing.Main.diagonal_revenue
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:33:41.742131+00:00
-- url     : https://prove2.me/theorems/36ef9fed-9f6f-4cfd-821d-3b6be60b3b68
-- title:
--   Lemma 3.4 — Diagonal revenue lower bound
-- statement:
--   For the explicitly constructed independent family, the diagonal menu is implementable and its actual expected revenue satisfies
--
--   $$\operatorname{Rev}(M)\ge\operatorname{Diag},\qquad \operatorname{OPT}\ge\operatorname{Diag}.$$
--
--   The contribution computed from the displayed probabilities and prices equals the closed expression (34):
--
--   $$\operatorname{Diag}=a\sigma\sum_{i=1}^{n-1}\left(\frac1{\omega_i}-\frac1{a\omega_{i+1}}\right)+\frac a{\omega_n}.$$
--
--   The revenue expectation includes the complete product type law. Off-diagonal payments are nonnegative and are not counted in the displayed diagonal lower bound. This supplies the attainable revenue used in the asymptotic separation.
--
--   Differences from the source:
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 3.4, printed pp.17–17 (PDF pp.19–19); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Diagonal

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 3.4 and (34), p.17 (PDF 19); the expectation is over the full product law. -/
theorem diagonal_revenue (k n : ℕ) (h : FamilyParameters k n) :
    ImplementsMenu (diagonalMenu k n) ∧
    diagonalRevenue k n = diagonalClosedForm k n ∧
    ENNReal.ofReal (diagonalRevenue k n) ≤ menuRevenue true (familyLaw k n) (diagonalMenu k n) ∧
    ENNReal.ofReal (diagonalRevenue k n) ≤ opt (familyLaw k n) := by sorry

end IndependentInfoPricing.Main
