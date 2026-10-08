-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_theorem_4_3_2
-- name    : KallenbergLP.AverageLP.theorem_4_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:33:49.196955+00:00
-- url     : https://prove2.me/theorems/0ef41c0e-7b24-4c09-83a9-a21bd9086284
-- title:
--   Theorem 4.3.2 — stationary policies correspond one-to-one to representatives, with (4.3.1) as inverse
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$. For a feasible solution $(x,y)$ of (4.2.11) let $\pi(x,y)$ be the stationary policy
--   $$\pi_{ia}(x,y):=\begin{cases}x_{ia}/\sum_ax_{ia},&i\in E_x,\\ y_{ia}/\sum_ay_{ia},&i\in E\setminus E_x,\end{cases}$$
--   of (4.3.1), and for a stationary policy $\pi^\infty$ let $(x(\pi),y(\pi))$ be the representative (4.3.2). Then the map $\pi\mapsto(x(\pi),y(\pi))$ is one-to-one, and (4.3.1) is its inverse:
--   $$\pi_{ia}\big(x(\pi),y(\pi)\big)=\pi_{ia}\qquad\text{for all }a\in A(i),\ i\in E.$$
--   Hence the stationary policies are in bijection with the set of representatives.
--
--   **Formalization Note** The set of representatives is by definition the image of the map, so "onto" is immediate; the statement records injectivity and the inverse formula.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 110, Theorem 4.3.2; (4.3.1), p. 108; (4.3.2), p. 109

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.3.2.** The mapping `π ↦ (x(π), y(π))` defined by (4.3.2) is a one-to-one mapping
of the stationary policies onto the set of representatives, with (4.3.1) as the inverse mapping:
it is injective, and `π_ia(x(π), y(π)) = π_ia` for every stationary policy `π^∞`, `a ∈ A`, `i ∈ E`.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 110, Theorem 4.3.2; representatives, p. 110; (4.3.1), p. 108.

**Formalization Note.** The set of representatives is by definition the image
`{(x(π), y(π))}`, so "onto" holds by definition; the content is injectivity and the inverse
formula. Both weight functions vanish off the admissible actions. -/
theorem theorem_4_3_2 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1) :
    (∀ π₁ π₂ : StatPolicy M,
      (xRep M β π₁, yRep M β π₁) = (xRep M β π₂, yRep M β π₂) → π₁ = π₂) ∧
    ∀ (π : StatPolicy M) (i : S) (a : A),
      dualPolicyWeight M (xRep M β π) (yRep M β π) i a = π.weight i a := by sorry

end KallenbergLP.AverageLP
