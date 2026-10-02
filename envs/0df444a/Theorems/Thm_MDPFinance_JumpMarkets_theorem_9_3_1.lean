-- Prove2me | Theorems.Thm_MDPFinance_JumpMarkets_theorem_9_3_1
-- name    : MDPFinance.JumpMarkets.theorem_9_3_1
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-09-27T23:28:07.524388+00:00
-- url     : https://prove2.me/theorems/ca728e09-713c-4a60-95a7-07754cc5ea3e
-- title:
--   Theorem 9.3.1 — continuous-time value equals the embedded discrete-time value
-- statement:
--   **Theorem 9.3.1** (p. 283).
--
--   a) For a Markov portfolio strategy $\pi = (\pi_t) = (f_n)$ we have
--      $V_\pi(t,x) = J_{\infty(f_n)}(t,x)$, $(t,x) \in E$.
--   b) It holds: $V = J_\infty$.
--
--   The reduction the whole section rests on. $V_\pi$ is an expectation of $U(X_T)$ over the
--   *continuous-time* wealth path; $J_{\infty(f_n)}$ is an infinite sum of one-stage rewards along the
--   *embedded jump chain*. a) says the two agree for each Markov strategy, and b) that the suprema
--   agree — the second needing the further step that a history-dependent strategy buys nothing, which
--   the book takes from Bertsekas and Shreve (1978, p. 216).
--
--   Both sides are built rather than carried abstractly, because the theorem *is* their
--   identification. b)'s two suprema are stated as least upper bounds against explicit sets of
--   achievable values, not as `sSup`, which for a set unbounded above would be $0$.
--
--   **Moderation note.** The draft's part b) compared two suprema over the *same* Markov strategies, so it was a corollary of a) rather than the book's `V = J_∞` (whose content is that history-dependent strategies buy nothing, via Bertsekas–Shreve); its a) held for arbitrary (non-measurable) `(f_n)`, and both sides were real Bochner integrals. Now `Pr` is the family of chain laws of all history-dependent strategies, a) is stated for measurable Markov `(f_n)`, and b) is `V = J_∞` with `V` the supremum over history-dependent strategies and `J_∞` over Markov policies, in `[0,∞]`.
-- source:
--   Bäuerle and Rieder, Markov Decision Processes with Applications to Finance, Universitext, Springer 2011, DOI 10.1007/978-3-642-18324-9, p. 283 (PDF 293), Theorem 9.3.1

import Mathlib
import Definitions.Def_MDPFinance_JumpMarkets_JumpMarket

open MeasureTheory
open scoped ENNReal

namespace MDPFinance.JumpMarkets

/-- **Theorem 9.3.1** (p. 283). a) For a Markov portfolio strategy `π = (π_t) = (f_n)`,
`V_π(t,x) = J_{∞(f_n)}(t,x)` on `E`. b) `V = J_∞`: the supremum of `V_π` over all
(history-dependent) strategies equals the value of the embedded discrete-time model. `Pr` is the
family of chain laws `ℙ^π_{tx}` (one for each strategy), pinned by `IsChainLaw`. -/
theorem theorem_9_3_1 {d : ℕ} (M : JumpMarket d)
    (Pr : HistPolicy d → ℝ × ℝ → Measure (ℕ → ℝ × ℝ))
    (hPr : ∀ g, M.IsChainLaw g (Pr g)) :
    (∀ f : ℕ → ℝ × ℝ → Control d, IsMarkovStrategy f →
      ∀ p ∈ M.E, M.Vpi (ofMarkov f) (Pr (ofMarkov f)) p = M.Jinfpi f (Pr (ofMarkov f)) p) ∧
    (∀ p ∈ M.E, M.V Pr p = M.Jinf Pr p) := by sorry

end MDPFinance.JumpMarkets
