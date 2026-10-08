-- Prove2me | Theorems.Thm_GloriaOtto_Variance_corollary_2_2
-- name    : GloriaOtto.Variance.corollary_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T05:44:59.03414+00:00
-- url     : https://prove2.me/theorems/14548db9-dcd8-410a-97bc-6799b21fe051
-- title:
--   Corollary 2.2 — G_T(x, y; a) ≤ h_T(x − y) for a bounded, radially symmetric, summable h_T uniform in a ∈ A_αβ
-- statement:
--   Let $d \ge 2$, $0 < \alpha \le \beta$. For every $T > 0$ there is a function $h_T : \mathbb Z^d \to \mathbb R$, depending only on $d, \alpha, \beta, T$, which is bounded, summable ($h_T \in \ell^1(\mathbb Z^d)$) and radially symmetric ($h_T(x) = h_T(x')$ whenever $|x| = |x'|$), such that
--   $$G_T(x,y;a) \le h_T(x-y)\qquad\text{for all } x,y\in\mathbb Z^d \text{ and all } a \in \mathcal A_{\alpha\beta}.$$
--
--   This is a pointwise decay bound, uniform in the coefficients but not in $T$. It justifies exchanging derivatives and sums in the proofs of Lemmas 2.4 and 2.6.
-- source:
--   Gloria, Otto, arXiv:1104.1291v1, Corollary 2.2, p. 19

import Mathlib
import Definitions.Def_GloriaOtto_Variance_Setup

open MeasureTheory ProbabilityTheory

namespace GloriaOtto.Variance

theorem corollary_2_2 (d : ℕ) (hd : 2 ≤ d) (α β : ℝ) (hα : 0 < α) (hαβ : α ≤ β) :
    ∀ T : ℝ, 0 < T → ∃ h : Site d → ℝ,
      (∃ M : ℝ, ∀ x, |h x| ≤ M) ∧ Summable h ∧
      (∀ x y : Site d, latNorm x = latNorm y → h x = h y) ∧
      ∀ a : Edge d → ℝ, InA α β a → ∀ x y : Site d, greenT a T x y ≤ h (x - y) := by sorry

end GloriaOtto.Variance
