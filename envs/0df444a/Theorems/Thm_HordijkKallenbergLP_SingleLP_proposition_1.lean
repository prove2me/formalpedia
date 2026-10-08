-- Prove2me | Theorems.Thm_HordijkKallenbergLP_SingleLP_proposition_1
-- name    : HordijkKallenbergLP.SingleLP.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:01:01.774715+00:00
-- url     : https://prove2.me/theorems/9d984d0f-7f9d-4473-95d8-b4e01f0cb62c
-- title:
--   Proposition 1 — φ is P(f)-harmonic, and the gain–bias equation holds on E_x
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$. Let $(x,y)$ be an optimal solution of the dual program, let $f(i)=a_i$ follow the selection rule of Theorem 7 ($x_{ia_i}>0$ for $i\in E_x$, $y_{ia_i}>0$ for $i\notin E_x$), and let $(\varphi,u)$ be an optimal solution of the primal program whose first component is the optimal average reward $\varphi$. Then
--   $$\sum_j(\delta_{ij}-p_{ia_ij})\varphi_j=0,\quad i\in E,\qquad \varphi_i+\sum_j(\delta_{ij}-p_{ia_ij})u_j=r_{ia_i},\quad i\in E_x .$$
--
--   It is the first of the three propositions of the proof of Theorem 7.
--
--   **Formalization Note** $(x,y)$ is only required to be optimal, not an extreme point.
-- source:
--   Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci. 25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, Proposition 1

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_HordijkKallenbergLP_SingleLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter Topology

namespace HordijkKallenbergLP.SingleLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proposition 1.** In the proof of Theorem 7 — `(x, y)` an optimal solution of the dual
program, `f(i) = a_i` chosen by the rule of Theorem 7, and `(φ, u)` an optimal solution of the
primal program, whose first component is the optimal average reward `φ` —
`Σ_j (δ_{ij} − p_{i a_i j}) φ_j = 0` for `i ∈ E`, and
`φ_i + Σ_j (δ_{ij} − p_{i a_i j}) u_j = r_{i a_i}` for `i ∈ E_x`.

Hordijk and Kallenberg, Linear Programming and Markov Decision Chains, Management Sci.
25(4):352–362 (1979), DOI 10.1287/mnsc.25.4.352, p. 357, Proposition 1.

**Formalization Note.** `(x, y)` need not be an extreme point here: the paper's proof uses only
optimality and complementary slackness. `Σ_j (δ_{ij} − p_{i a_i j}) v_j` is written
`v_i − Σ_j p_{i a_i j} v_j`. -/
theorem proposition_1 (M : StationaryMDP S A) [Nonempty S]
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hopt : IsDualOptimal M β z)
    (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) (hsel : IsSelection M z.1 z.2 f hf)
    (u : S → ℝ) (hP : IsPrimalOptimal M β (optGainInf M) u) :
    (∀ i : S, optGainInf M i - ∑ j, M.trans i (f i) j * optGainInf M j = 0) ∧
      ∀ i ∈ Ex M z.1,
        optGainInf M i + (u i - ∑ j, M.trans i (f i) j * u j) = M.reward i (f i) := by sorry

end HordijkKallenbergLP.SingleLP
