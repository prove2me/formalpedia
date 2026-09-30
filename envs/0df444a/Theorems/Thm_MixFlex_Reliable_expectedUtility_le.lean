-- Prove2me | Theorems.Thm_MixFlex_Reliable_expectedUtility_le
-- name    : MixFlex.Reliable.expectedUtility_le
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T22:01:19.757212+00:00
-- url     : https://prove2.me/theorems/fdc82ea0-dc47-4fe6-ba5e-4ab71e6d83b8
-- title:
--   Proof of Proposition 4(i) — $E[u(w^{SD}(K))]\le E[u(w^{SF}(\sum_n K_n))]$ for every nondecreasing utility
-- statement:
--   In the perfectly reliable SD/SF model with a common margin $p>0$, common cost $c>0$ and nonnegative, measurable demand on a probability space, let $u:\mathbb R\to\mathbb R$ be any nondecreasing utility function (the class $U_1$ of §3.3) and let $K=(K_1,\dots,K_N)$ be a nonnegative dedicated investment. Then
--   $$
--   E\big[u\big(w^{SD}(K)\big)\big]\le E\Big[u\Big(w^{SF}\Big(\sum_{n=1}^N K_n\Big)\Big)\Big].
--   $$
--
--   Applied to an optimal SD investment, this shows that the SF network, at the same unit cost, can do at least as well as SD for every decision maker who prefers more wealth to less.
--
--   **Formalization Note** No integrability hypothesis is needed: for $K\ge 0$ and nonnegative demand both wealths lie almost surely in $[w_0-c\sum_nK_n,\;w_0+p\sum_nK_n]$, and a monotone $u$ is measurable and bounded there, so both expectations are genuine Lebesgue integrals. No concavity, continuity or strict monotonicity of $u$ is assumed.
-- source:
--   Tomlin and Wang, On the value of mix flexibility and dual sourcing in unreliable newsvendor networks, Manufacturing Service Oper. Management 7(1), 2005, p. 53, Appendix A, proof of PROPOSITION 4(i) (as quoted from Levy 1992, Equation (4)); p. 45, §3.3 (U_1)

import Mathlib
import Definitions.Def_MixFlex_Reliable_Model

open MeasureTheory

namespace MixFlex.Reliable
theorem expectedUtility_le (P : Params) (hP : P.Standing) {N : ℕ} {Ω : Type*}
    [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → Fin N → ℝ) (hS : Setting μ X)
    (u : ℝ → ℝ) (hu : Monotone u) (K : Fin N → ℝ) (hK : ∀ n, 0 ≤ K n) :
    expectedUtility μ u (wealthSD P X K) ≤
      expectedUtility μ u (wealthSF P X P.c (∑ n, K n)) := by sorry
end MixFlex.Reliable
