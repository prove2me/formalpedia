-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_abstract_bound
-- name    : IndependentInfoPricing.Main.abstract_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:07.766336+00:00
-- url     : https://prove2.me/theorems/6a0d6244-e197-4327-bbf3-8efd938a052e
-- title:
--   Proposition 4.22 — Abstract bound
-- statement:
--   For a product payoff law with finite attained branch monopoly revenues, let $\Theta,t>0$ and let real constants $\kappa,\kappa_B\ge0$ satisfy all five estimates
--
--   $$\mathbb EU_+\le\kappa\Theta,\quad\mathbb EA\le\kappa,\quad\mathbb E\varphi\le16R,\quad\mathbb E\varphi_-\le35R,\quad\mathbb EB\le\kappa_B.$$
--
--   Then
--
--   $$\operatorname{OPT}^{\rm rel}\le\kappa\Theta+(\kappa+2)\bigl(35+16(\kappa_B+2)\bigr)R.$$
--
--   The five estimates are hypotheses of this intermediate result only. They are not assumptions in the main theorem. Nonnegativity of the two constants is already implied by their real expectation bounds in the source and is made explicit when using nonnegative extended arithmetic.
--
--   Differences from the source:
--   - generalization: continuously differentiable marginal densities in the upper-bound section → probability marginals with no atom at zero and finite monopoly-price attainment on occurring branches; reason: these intermediate arguments use product laws and branch revenues without differentiability; every source instance satisfies these hypotheses
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
--   - encoding: real nonnegative expectations bounded above by kappa and kappa_B → nonnegative real constants explicitly required when embedding the five estimates into extended nonnegative reals; reason: the source real expectation bounds already imply these signs; the explicit clauses prevent ofReal from discarding a negative upper bound
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Proposition 4.22, printed pp.46–46 (PDF pp.48–48); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Analysis

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Proposition 4.22, p.46 (PDF 48), all five assumptions in (78), exact (79). -/
theorem abstract_bound {Q : ℕ} (F : Marginals (Fin Q)) (hF : BranchScope F)
    (Θ t κ κB : ℝ) (hΘ : 0 < Θ) (ht : 0 < t)
    (hu : signExpectation F (uPlus F Θ) ≤ ENNReal.ofReal (κ * Θ))
    (ha : signExpectation F (tailsPlus F Θ) ≤ ENNReal.ofReal κ)
    (hφ : signExpectation F (phi F) ≤ 16 * benchmark (productLaw F))
    (hφm : signExpectation F (phiMinus F t) ≤ 35 * benchmark (productLaw F))
    (hb : signExpectation F (tailsMinus F t) ≤ ENNReal.ofReal κB)
    (hκ : 0 ≤ κ) (hκB : 0 ≤ κB) :
    optRel (productLaw F) ≤ ENNReal.ofReal (κ * Θ) +
      ENNReal.ofReal ((κ + 2) * (35 + 16 * (κB + 2))) * benchmark (productLaw F) := by sorry

end IndependentInfoPricing.Main
