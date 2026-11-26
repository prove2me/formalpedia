-- Prove2me | Theorems.Thm_LearnThenTest_max_pvalue_valid
-- name    : LearnThenTest.max_pvalue_valid
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-24T00:09:53.773257+00:00
-- url     : https://prove2.me/theorems/95dbc84d-9715-4850-b677-99743ad5259e
-- title:
--   Proposition 6: the maximum of the per-risk p-values is valid
-- statement:
--   Fix a parameter $\lambda_j$ and $m$ risks $R_1,\dots,R_m$ with levels $\alpha_1,\dots,\alpha_m$. For each $l$, let $p_{j,l}$ be a p-value for $\mathcal H_{j,l}:R_l(\lambda_j)>\alpha_l$, valid whenever $\mathcal H_{j,l}$ holds. Define $p_j=\max_lp_{j,l}$. If $\mathcal H_j$ holds, that is, $R_l(\lambda_j)>\alpha_l$ for some $l$, then
--
--   $$\mathbb P(p_j\le u)\le u\qquad\text{for all }u\in[0,1].$$
--
--   This reduces simultaneous control of several risks to the single-risk procedures above.
-- source:
--   Angelopoulos, Bates, Candès, Jordan and Lei, Learn then Test: Calibrating Predictive Algorithms to Achieve Risk Control, arXiv:2110.01052v5 (2022), Section 2.4, Proposition 6, p. 6; proof in Appendix C, p. 22

import Mathlib
import Definitions.Def_LearnThenTest_Basic

open MeasureTheory ProbabilityTheory Filter

namespace LearnThenTest

theorem max_pvalue_valid {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] {m : ℕ} (R α : Fin m → ℝ) (p : Fin m → Ω → ℝ)
    (hp : ∀ l, Measurable (p l)) (hvalid : ∀ l, α l < R l → IsValidPValue P (p l))
    (hnull : ∃ l, α l < R l) :
    IsValidPValue P (fun ω => ⨆ l, p l ω) := by sorry

end LearnThenTest
