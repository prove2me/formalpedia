-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_theorem_4_2_2
-- name    : KallenbergLP.AverageLP.theorem_4_2_2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:33:21.340769+00:00
-- url     : https://prove2.me/theorems/416fb668-8f08-4643-97da-2e81b94aa614
-- title:
--   Theorem 4.2.2 — the AMD-value-vector is the smallest AMD-superharmonic vector
-- statement:
--   In a finite Markov decision model with stochastic transition rows, let $\phi_i=\sup_R\phi_i(R)$ be the AMD-value-vector, the supremum over all policies of the lim inf average reward. A vector $\tilde\phi$ is AMD-superharmonic if there is a vector $\tilde u$ with
--   $$\tilde\phi_i\ge\sum_jp_{iaj}\tilde\phi_j\quad\text{and}\quad\tilde\phi_i+\tilde u_i\ge r_{ia}+\sum_jp_{iaj}\tilde u_j\qquad\text{for all }a\in A(i),\ i\in E.$$
--   Then $\phi$ is AMD-superharmonic, and $\phi\le\tilde\phi$ componentwise for every AMD-superharmonic vector $\tilde\phi$.
--
--   This is what makes the linear program (4.2.10), which minimises $\sum_j\beta_j\tilde\phi_j$ over superharmonic pairs, have $\phi$ as the first component of its optimal solutions.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 99, Theorem 4.2.2; Definition 4.2.1, pp. 98–99

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.2.2.** The AMD-value-vector `φ` is the smallest AMD-superharmonic vector: `φ` is
AMD-superharmonic, and `φ ≤ φ̃` componentwise for every AMD-superharmonic `φ̃`.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 99, Theorem 4.2.2.

**Formalization Note.** `φ_i = sup_R φ_i(R)` (`optGainInf`) is the supremum over all
history-dependent randomized policies of the lim inf average reward. -/
theorem theorem_4_2_2 (M : StationaryMDP S A) :
    IsAMDSuperharmonic M (optGainInf M) ∧
      ∀ φ' : S → ℝ, IsAMDSuperharmonic M φ' → ∀ i, optGainInf M i ≤ φ' i := by sorry

end KallenbergLP.AverageLP
