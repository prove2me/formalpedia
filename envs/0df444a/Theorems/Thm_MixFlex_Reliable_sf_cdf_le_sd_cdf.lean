-- Prove2me | Theorems.Thm_MixFlex_Reliable_sf_cdf_le_sd_cdf
-- name    : MixFlex.Reliable.sf_cdf_le_sd_cdf
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:00:34.205071+00:00
-- url     : https://prove2.me/theorems/56d27885-9b19-4ebf-8db5-d45b71465552
-- title:
--   Proof of Proposition 4(i) — $F_{W^{SF}}\le F_{W^{SD}}$: the pooled SF wealth first-order dominates the SD wealth
-- statement:
--   In the perfectly reliable SD/SF model with nonnegative, measurable demand on a probability space, let $K=(K_1,\dots,K_N)$ be a dedicated investment and let the flexible network invest $\sum_n K_n$ at the common cost $c$. Then for every level $w\in\mathbb R$,
--   $$
--   \mathbb P\Big(w^{SF}\Big(\sum_{n=1}^N K_n\Big)\le w\Big)\le\mathbb P\big(w^{SD}(K)\le w\big),
--   $$
--   that is, the distribution function of the SF wealth lies below that of the SD wealth, and the SF wealth first-order stochastically dominates the SD wealth.
--
--   This is the step of the proof of Proposition 4 from which the expected-utility and CVaR comparisons follow.
--
--   **Formalization Note** The page states the inequality for the profits $\tilde W=W-w_0$; shifting both by the same constant $w_0$ does not change it, so it is stated for terminal wealth.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 53, Appendix A, proof of PROPOSITION 4(i), after (A-6)

import Mathlib
import Definitions.Def_MixFlex_Reliable_Model

open MeasureTheory

namespace MixFlex.Reliable
theorem sf_cdf_le_sd_cdf (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (hS : Setting μ X)
    (K : Fin N → ℝ) (w : ℝ) :
    μ.real {ω | wealthSF P X P.c (∑ n, K n) ω ≤ w} ≤ μ.real {ω | wealthSD P X K ω ≤ w} := by sorry
end MixFlex.Reliable
