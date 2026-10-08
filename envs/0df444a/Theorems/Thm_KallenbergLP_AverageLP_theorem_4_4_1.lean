-- Prove2me | Theorems.Thm_KallenbergLP_AverageLP_theorem_4_4_1
-- name    : KallenbergLP.AverageLP.theorem_4_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T10:34:29.288251+00:00
-- url     : https://prove2.me/theorems/0a878637-0897-4073-8d1c-0f83d30685b9
-- title:
--   Theorem 4.4.1 — the system (4.4.1) is solvable and determines $\phi(f^\infty)$ and $u(f^\infty)$
-- statement:
--   Let $f^\infty$ be any pure and stationary policy in a finite Markov decision model with stochastic transition rows. Then the linear system
--   $$(I-P(f))\tilde\phi=0,\qquad \tilde\phi+(I-P(f))\tilde u=r(f),\qquad \tilde u+(I-P(f))\tilde z=0 \tag{4.4.1}$$
--   has a solution $(\tilde\phi,\tilde u,\tilde z)$, and every solution satisfies $\tilde\phi=\phi(f^\infty)$ and $\tilde u=u(f^\infty)$, where $\phi(f^\infty)$ is the average reward vector of $f^\infty$ and $u(f^\infty)=D(f)r(f)$ with $D(f)$ the deviation matrix of $P(f)$.
--
--   This characterises the gain and bias of a fixed pure policy by a finite linear system and is the evaluation step of multichain policy improvement.
-- source:
--   Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 118, Theorem 4.4.1; (2.5.5), p. 34

import Mathlib
import Definitions.Def_MarkovDecisionProcesses_AverageReward
import Definitions.Def_BlackwellDiscreteDP_NearOne_LimitMatrix
import Definitions.Def_KallenbergLP_AverageLP_Model
open MarkovDecisionProcesses BlackwellDiscreteDP.NearOne Matrix Filter

namespace KallenbergLP.AverageLP

variable {S A : Type*} [Fintype S] [Fintype A] [DecidableEq S] [DecidableEq A]

/-- **Theorem 4.4.1.** For any pure and stationary policy `f^∞`, the linear system (4.4.1)
`(I − P(f)) φ̃ = 0`, `φ̃ + (I − P(f)) ũ = r(f)`, `ũ + (I − P(f)) z̃ = 0`
has a feasible solution `(φ̃, ũ, z̃)`. Moreover any feasible solution of (4.4.1) satisfies
`φ̃ = φ(f^∞)` and `ũ = u(f^∞)`.

Kallenberg, Linear Programming and Finite Markovian Control Problems, Mathematical Centre Tracts 148, Mathematisch Centrum, Amsterdam 1983, p. 118, Theorem 4.4.1; `u(f^∞) = D(f)r(f)`, (2.5.5), p. 34.

**Formalization Note.** `φ(f^∞)` is the lim inf average reward of the pure stationary policy and
`u(f^∞) = D(f) r(f)` with the deviation matrix of Definition 2.4.2. -/
theorem theorem_4_4_1 (M : StationaryMDP S A) (f : S → A) (hf : ∀ i, f i ∈ M.admissible i) :
    (∃ φ u w : S → ℝ, (1 - Pf M f) *ᵥ φ = 0 ∧ φ + (1 - Pf M f) *ᵥ u = rf M f ∧
        u + (1 - Pf M f) *ᵥ w = 0) ∧
    ∀ φ u w : S → ℝ, (1 - Pf M f) *ᵥ φ = 0 → φ + (1 - Pf M f) *ᵥ u = rf M f →
        u + (1 - Pf M f) *ᵥ w = 0 →
      φ = (fun i => gainInf (stationaryPolicy M f hf) i) ∧ u = uPure M f := by sorry

end KallenbergLP.AverageLP
