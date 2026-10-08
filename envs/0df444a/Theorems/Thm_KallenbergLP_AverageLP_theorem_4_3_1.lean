-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_theorem_4_3_1
-- name    : KallenbergLP.AverageLP.theorem_4_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T10:33:49.900872+00:00
-- url     : https://prove2.me/theorems/d911847d-3e5a-4387-9aec-dad7d4bde096
-- title:
--   Theorem 4.3.1 — $(x(\pi),y(\pi))$ is feasible for the multichain LP
-- statement:
--   Let $\beta_j>0$ with $\sum_j\beta_j=1$ and let $\pi^\infty$ be a stationary policy. Let $E_1,\dots,E_m$ be the ergodic sets and $F$ the set of transient states of the chain $P(\pi)$, let $P^*(\pi)=(p^*_{k\ell}(\pi))$ be its stationary (Cesàro limit) matrix and $D(\pi)=(d_{k\ell}(\pi))$ its deviation matrix. Define
--   $$\gamma_i:=0\ (i\in F),\qquad \gamma_i:=\max_{\ell\in E_j}\Big\{-\sum_k\beta_kd_{k\ell}(\pi)\Big/\sum_{k\in E_j}p^*_{k\ell}(\pi)\Big\}\ (i\in E_j),$$
--   and
--   $$x_{ia}(\pi):=[\beta^TP^*(\pi)]_i\,\pi_{ia},\qquad y_{ia}(\pi):=[\beta^TD(\pi)+\gamma^TP^*(\pi)]_i\,\pi_{ia}.$$
--   Then $(x(\pi),y(\pi))$ is a feasible solution of the linear program (4.2.11).
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 109, Theorem 4.3.1; (4.3.2)–(4.3.3), p. 109

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.3.1.** For every stationary policy `π^∞`, `(x(π), y(π))`, defined by (4.3.2) with
`γ` of (4.3.3), is a feasible solution of the linear programming problem (4.2.11).

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 109, Theorem 4.3.1; (4.3.2)–(4.3.3), p. 109.

**Formalization Note.** `P*(π)` is the Cesàro limit of the powers of `P(π)` and
`D(π) = (I − P(π) + P*(π))^{-1} − P*(π)`; that the limit exists and the matrix is invertible is
Theorem 2.4.1 and is not assumed. -/
theorem theorem_4_3_1 (M : StationaryMDP S A)
    (β : S → ℝ) (hβpos : ∀ j, 0 < β j) (hβsum : ∑ j, β j = 1) (π : StatPolicy M) :
    (xRep M β π, yRep M β π) ∈ dualFeasible M β := by sorry

end KallenbergLP.AverageLP
