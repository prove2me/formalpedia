-- Prove2me | Theorems.Thm_MixFlex_Reliable_cvar_le
-- name    : MixFlex.Reliable.cvar_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:03:05.360888+00:00
-- url     : https://prove2.me/theorems/a6cf1ecb-5a5b-425b-9f8c-0a4a29b022e4
-- title:
--   Proof of Proposition 4(ii) — $V^{SD}_{CVaR}(K)\le V^{SF}_{CVaR}(\sum_n K_n)$
-- statement:
--   In the perfectly reliable SD/SF model with a common margin $p>0$, common cost $c>0$, percentile $\eta\in(0,1]$ and nonnegative, measurable demand on a probability space, let $K=(K_1,\dots,K_N)$ be a nonnegative dedicated investment. Then for every threshold $v\in\mathbb R$ there is a threshold $v'\in\mathbb R$ with
--   $$
--   w_0+v+\frac1\eta E\big[\min\{\tilde W^{SD}(K)-v,0\}\big]\le w_0+v'+\frac1\eta E\Big[\min\Big\{\tilde W^{SF}\Big(\sum_{n=1}^NK_n\Big)-v',0\Big\}\Big],
--   $$
--   where $\tilde W=W-w_0$ denotes profit.
--
--   With $V_{CVaR}$ as in (7) (a maximum over $v$), this is $V^{SD}_{CVaR}(K_1,\dots,K_N)\le V^{SF}_{CVaR}(\sum_nK_n)$, the CVaR half of Proposition 4(ii).
--
--   **Formalization Note** The comparison of the maxima over $v$ in (7) is stated as: every value of the SD bracket is matched or exceeded by some value of the SF bracket. This is the page's inequality between the two maxima without a real supremum and without asserting that the maxima are attained. The paper's route through second-order stochastic dominance and Levy (1992, Theorem 3) is not formalized; its conclusion is.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 53, Appendix A, proof of PROPOSITION 4(ii) (as quoted from Levy 1992, Theorem 3); p. 40, (7)

import Mathlib
import Definitions.Def_MixFlex_Reliable_Model

open MeasureTheory

namespace MixFlex.Reliable
theorem cvar_le (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (hS : Setting μ X)
    (K : Fin N → ℝ) (hK : ∀ n, 0 ≤ K n) :
    ∀ v : ℝ, ∃ v' : ℝ, cvarObjective P μ (wealthSD P X K) v ≤
      cvarObjective P μ (wealthSF P X P.c (∑ n, K n)) v' := by sorry
end MixFlex.Reliable
