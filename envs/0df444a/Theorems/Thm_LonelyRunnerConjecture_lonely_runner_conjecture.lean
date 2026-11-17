-- Prove2me | Theorems.Thm_LonelyRunnerConjecture_lonely_runner_conjecture
-- name    : LonelyRunnerConjecture.lonely_runner_conjecture
-- status  : Open
-- author  : @Lucas
-- created : 2026-11-17T01:16:31.2934+00:00
-- url     : https://prove2.me/theorems/27e04238-c7d0-4736-9c4b-df5c3b1bf0e6
-- title:
--   Lonely runner conjecture
-- statement:
--   **The lonely runner conjecture.** Runners start together at $0$ on a circular track of length $1$, each with a distinct positive integer speed. For every $k\in\mathbb N$ and every set of $k$ distinct positive integer speeds $v_1,\dots,v_k$ there is a time $t$ at which every runner is at distance at least $\frac{1}{k+1}$ from the start:
--   $$\forall k,\ \forall\{v_1,\dots,v_k\}\subset\mathbb Z_{>0}\text{ distinct},\ \exists t\in\mathbb R,\ \forall i,\ \|tv_i\|\ge\tfrac{1}{k+1}.$$
--   Equivalently, every runner is sometimes *lonely*. The threshold $\frac{1}{k+1}$ is best possible (Dirichlet approximation). A counterexample — a set of $k\ge2$ distinct positive integers such that at every time some runner is within $<\frac{1}{k+1}$ of $0$ — would disprove the conjecture; this is the task posed by Epoch AI. The cases $k=0,1$ are trivial.
--
--   **Formalization Note** Speeds are a `Finset ℕ` of positive integers (distinctness automatic); $\|x\|$ is `distToNearestInt`. The statement is `∀ k, LRC k`.
-- source:
--   Epoch AI, FrontierMath: Open Problems — The Lonely Runner Conjecture, https://epoch.ai/frontiermath/open-problems/lonely-runner (Prompt and About sections).

import Mathlib
import Definitions.Def_LonelyRunnerConjecture_Defs

namespace LonelyRunnerConjecture

theorem lonely_runner_conjecture : ∀ k : ℕ, LRC k := by sorry

end LonelyRunnerConjecture
