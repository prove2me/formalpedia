-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_weighted_counting
-- name    : IndependentInfoPricing.Main.weighted_counting
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:17.583164+00:00
-- url     : https://prove2.me/theorems/b6a169de-997d-4380-9ab1-48e59e157122
-- title:
--   Lemma 4.23 — Weighted counting
-- statement:
--   Let independent Bernoulli coordinates have arbitrary parameters $\alpha_i\in[0,1]$. For weights $w_i,w'_i\in[0,1]$, set $A(\xi)=\sum_i w_i\xi_i$ and $B(\xi)=\sum_iw'_i(1-\xi_i)$. Every nonnegative submodular function $\varphi$ of the signs satisfies both
--
--   $$\mathbb E[(1+A)\varphi]\le(\mathbb EA+2)\mathbb E\varphi,$$
--
--   $$\mathbb E[(1+A)(1+B)\varphi]\le(\mathbb EA+2)(\mathbb EB+2)\mathbb E\varphi.$$
--
--   Expectations are exact finite product-Bernoulli sums. Neither monotonicity nor normalization at the empty set is assumed. These inequalities supply the dimension-independent coefficients in the abstract revenue bound.
--
--   Differences from the source:
--   - encoding: expectations of independent Bernoulli coordinates → finite product-weighted sums over positive-coordinate sets; reason: the exact product Bernoulli law includes probabilities zero and one and needs no additional integrability assumptions
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.23, printed pp.46–46 (PDF pp.48–48); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Analysis

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 4.23, pp.46–47 (PDF 48–49), both inequalities; no monotonicity. -/
theorem weighted_counting {Q : ℕ} (α w w' : Fin Q → ℝ)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1)
    (hw : ∀ i, w i ∈ Set.Icc (0 : ℝ) 1) (hw' : ∀ i, w' i ∈ Set.Icc (0 : ℝ) 1)
    (φ : Finset (Fin Q) → ℝ) (hφ : ∀ S, 0 ≤ φ S)
    (hs : NonmonotoneSubmod.Shared.Submodular φ) :
    cubeExpectation α (fun S => (1 + countPositive w S) * φ S) ≤
      (cubeExpectation α (countPositive w) + 2) * cubeExpectation α φ ∧
    cubeExpectation α (fun S => (1 + countPositive w S) * (1 + countNegative w' S) * φ S) ≤
      (cubeExpectation α (countPositive w) + 2) * (cubeExpectation α (countNegative w') + 2) * cubeExpectation α φ := by sorry

end IndependentInfoPricing.Main
