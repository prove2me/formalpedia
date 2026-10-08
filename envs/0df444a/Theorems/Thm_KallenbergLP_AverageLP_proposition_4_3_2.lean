-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_proposition_4_3_2
-- name    : KallenbergLP.AverageLP.proposition_4_3_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:33:56.365213+00:00
-- url     : https://prove2.me/theorems/e8dd026d-4cab-4829-989e-ec46225874ae
-- title:
--   Proposition 4.3.2 — $E_x$ is closed under $P(\pi(x,y))$
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$ and let $(x,y)$ be an optimal solution of the linear program (4.2.11). Then $E_x=\{i\mid\sum_ax_{ia}>0\}$ is closed under the transition matrix $P(\pi(x,y))$ of the stationary policy (4.3.1):
--   $$p_{k\ell}(\pi(x,y))=\sum_ap_{ka\ell}\pi_{ka}(x,y)=0\qquad\text{for }k\in E_x,\ \ell\notin E_x.$$
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 113, Proposition 4.3.2 (proof of Theorem 4.3.3)

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Proposition 4.3.2** (proof of Theorem 4.3.3, part 2). Let `(x, y) = z` be an optimal solution
of (4.2.11) (`β_j > 0`, `Σ_j β_j = 1`). Then `E_x` is closed under `P(π(x, y))`, the transition
matrix of the stationary policy (4.3.1).

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 113, Proposition 4.3.2. -/
theorem proposition_4_3_2 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1)
    (z : (Pair M → ℝ) × (Pair M → ℝ)) (hopt : IsDualOptimal M β z) :
    IsClosedUnder (weightMatrix M (dualPolicyWeight M z.1 z.2)) (Ex M z.1) := by sorry

end KallenbergLP.AverageLP
