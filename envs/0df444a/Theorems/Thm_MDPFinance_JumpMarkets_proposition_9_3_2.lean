-- Prove2me | Theorems.Thm_MDPFinance_JumpMarkets_proposition_9_3_2
-- name    : MDPFinance.JumpMarkets.proposition_9_3_2
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-09-27T23:28:53.137151+00:00
-- url     : https://prove2.me/theorems/6fb7bbb4-571d-4746-be59-f52200651ba9
-- title:
--   Proposition 9.3.2 — bounding function and explicit contraction modulus for the jump market
-- statement:
--   **Proposition 9.3.2** (p. 284).
--
--   a) The function $b(t,x) := e^{\gamma(T-t)}(1+x)$ is a bounding function for the discrete-time
--      Markov Decision Model for all $\gamma \ge 0$.
--   b) We obtain
--      $$ \alpha_b \le \frac{\lambda(1+\bar y)}{\gamma + \lambda - \barμ}\Big(1 - e^{-T(\gamma+\lambda-\barμ)}\Big) =: \alpha_\gamma. \tag{9.14} $$
--      In particular for $\gamma$ large enough, we have $\alpha_\gamma < 1$ and the discrete-time model
--      is contracting.
--
--   What makes Chapter 7's contracting theory applicable, and so the reason the value function is a
--   *unique* fixed point rather than merely a fixed point.
--
--   $\alpha_\gamma$ is an **explicit formula** in $\gamma, \lambda, T, \bar y, \barμ$, not an abstract
--   "sufficiently small" constant. That is why "for $\gamma$ large enough" is stated as a genuine
--   existence claim — some explicit threshold beyond which $\alpha_\gamma < 1$ — rather than a vague
--   assertion: the factor $\lambda(1+\bar y)/(\gamma+\lambda-\barμ)$ tends to $0$ as
--   $\gamma \to \infty$ while the bracket stays bounded by $1$.
--
--   The reward is non-negative and **unbounded** (p. 282), which is exactly why a bounding function is
--   needed rather than a sup-norm argument.
--
--   **Moderation note.** `α_γ`'s formula divides by `γ + λ − \barμ`; at `γ + λ = \barμ` it is a junk `0` and the claim `α_b ≤ α_γ` false, so b) is stated for `γ + λ ≠ \barμ` (the book's implicit domain of (9.14)); the bounding-function integral is a Lebesgue integral; the "large `γ`" clause is unchanged.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 284 (PDF 294), Proposition 9.3.2

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory

namespace MDPFinance.JumpMarkets

/-- **Proposition 9.3.2** (p. 284). a) `b(t,x) := e^{γ(T-t)}(1+x)` is a bounding function for
the discrete-time model for all `γ ≥ 0`. b) `α_b ≤ α_γ` **(9.14)** (for `γ + λ ≠ \barμ`, where the
formula is defined); in particular for `γ` large enough `α_γ < 1` and the model is contracting. -/
theorem proposition_9_3_2 {d : ℕ} (M : JumpMarket d) :
    (∀ gamma : ℝ, 0 ≤ gamma → ∃ alpha : ℝ, M.IsBoundingFunction (M.bfun gamma) alpha) ∧
    (∀ gamma : ℝ, 0 ≤ gamma → gamma + M.lam ≠ M.mubar →
      M.IsBoundingFunction (M.bfun gamma) (M.alphaGamma gamma)) ∧
    (∃ gamma0 : ℝ, 0 ≤ gamma0 ∧ ∀ gamma : ℝ, gamma0 ≤ gamma →
      M.alphaGamma gamma < 1 ∧ M.IsBoundingFunction (M.bfun gamma) (M.alphaGamma gamma)) := by sorry

end MDPFinance.JumpMarkets
