-- Prove2me | Theorems.Thm_NonsmoothQN_LineSearch_nonterminating_bracket
-- name    : NonsmoothQN.LineSearch.nonterminating_bracket
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T12:22:50.130231+00:00
-- url     : https://prove2.me/theorems/9810cdfc-f69e-4ddf-8979-c4f93605d2e5
-- title:
--   §4.1, proof of Theorem 4.7, pp. 147–148 — no termination ⇒ eventually 0 < α, β < ∞, A(α) holds, A(β) fails
-- statement:
--   Let $h$ satisfy Assumption 4.1 with slope $s<0$, let $0<c_1<c_2<1$, and run Algorithm 4.6, with brackets $[\alpha_n,\beta_n]$ before trial $n$. If the line search does not terminate, then there is $N$ such that for every $n\ge N$:
--
--   1. the upper bound $\beta_n$ is finite;
--   2. the lower bound is positive, $\alpha_n>0$;
--   3. the Armijo condition holds at the lower bound, $h(\alpha_n)<c_1s\alpha_n$;
--   4. the Armijo condition fails at the upper bound, $h(\beta_n)\ge c_1s\beta_n$.
--
--   These are exactly the hypotheses of Lemma 4.4 on every late bracket, which is how the nonzero-measure claim of Theorem 4.7 follows.
-- source:
--   Lewis, Overton, Nonsmooth optimization via quasi-Newton methods, Math. Program. Ser. A 141 (2013) 135–163, pp. 147–148, proof of Theorem 4.7 (first two paragraphs)

import Mathlib
import Definitions.Def_NonsmoothQN_LineSearch_Basic

open Filter Topology MeasureTheory Set

namespace NonsmoothQN.LineSearch

/-- Proof of Theorem 4.7, pp. 147–148. If Algorithm 4.6 does not terminate, then eventually the
upper bound `β` is finite, the lower bound `α` is positive, `A(α)` holds and `A(β)` fails. -/
theorem nonterminating_bracket (h : ℝ → ℝ) (c₁ c₂ s : ℝ)
    (hA41 : Assumption41 h s) (hc₁ : 0 < c₁) (hc₁₂ : c₁ < c₂) (hc₂ : c₂ < 1)
    (hnt : ¬ Terminates h c₁ c₂ s) :
    ∃ N : ℕ, ∀ n ≥ N, ∃ b : ℝ, (lsRun h c₁ c₂ s n).β = (b : WithTop ℝ) ∧
      0 < (lsRun h c₁ c₂ s n).α ∧ ArmijoA h c₁ s (lsRun h c₁ c₂ s n).α ∧
      ¬ ArmijoA h c₁ s b := by sorry

end NonsmoothQN.LineSearch
