-- Prove2me | Theorems.Thm_IndependentInfoPricing_Main_weighted_shielding
-- name    : IndependentInfoPricing.Main.weighted_shielding
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:34:20.355333+00:00
-- url     : https://prove2.me/theorems/691639a6-15ec-44bc-9bed-995da87804c1
-- title:
--   Lemma 4.28 — Weighted shielding
-- statement:
--   Let $\xi_i$ be independent Bernoulli variables with parameters $\alpha_i\in[0,1]$, and independently draw nonnegative magnitudes $D_i$ from a product of arbitrary probability laws. For $t>0$ set $\overline W_i=0$ if $\xi_i=1$ and $\overline W_i=\min(D_i,t)$ otherwise. Suppose $\sum_i\mathbb E\overline W_i=4t$. Every nonnegative, nondecreasing submodular function $\varphi$ of the sign vector satisfies
--
--   $$\mathbb E\!\left[\varphi(\xi)1_{\sum_i\overline W_i\ge t}\right]\ge(1-4e^{-2})\mathbb E\varphi(\xi).$$
--
--   The expectation on the left uses the actual joint sign/magnitude product model. It does not assume the shielding event is independent of the set function. This is the weighted probability bound needed to transfer the negative core.
--
--   Differences from the source:
--   - encoding: independent censored variables from coordinate sign/magnitude draws → product magnitude law independent of the product Bernoulli signs, summed over the sign sets; reason: retains the source joint product construction and its correlation with the shielding event
--   - encoding: real expected revenues and independent coordinates indexed by [Q] → nonnegative extended integrals and suprema with coordinates indexed by Fin Q; reason: preserves arbitrary real product laws and infinite revenues without default-zero integration; Fin Q only relabels the finite states
-- source:
--   Hu Fu, Chenshuo Guo, STOC 2027 submission #1459 (October 2026), Lemma 4.28, printed pp.51–51 (PDF pp.53–53); https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1459.pdf

import Definitions.Def_IndependentInfoPricing_Main_Analysis

open MeasureTheory
open scoped BigOperators ENNReal
noncomputable section

namespace IndependentInfoPricing.Main

/-- Lemma 4.28, pp.51–52 (PDF 53–54), (95)–(96), joint product signs and magnitudes. -/
theorem weighted_shielding {Q : ℕ} (α : Fin Q → ℝ)
    (hα : ∀ i, α i ∈ Set.Icc (0 : ℝ) 1) (D : Marginals (Fin Q)) (hD : nonnegativeLaws D)
    (t : ℝ) (ht : 0 < t)
    (hmean : (∑ i, ENNReal.ofReal (1 - α i) * cappedMean (D i) t) = ENNReal.ofReal (4 * t))
    (φ : Finset (Fin Q) → ℝ) (hφ : ∀ S, 0 ≤ φ S)
    (hm : Monotone φ) (hs : NonmonotoneSubmod.Shared.Submodular φ) :
    ENNReal.ofReal (1 - 4 * Real.exp (-2)) * ENNReal.ofReal (cubeExpectation α φ) ≤
      shieldingExpectation α D t φ := by sorry

end IndependentInfoPricing.Main
