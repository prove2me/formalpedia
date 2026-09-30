-- Prove2me | Theorems.Thm_KellyStochasticNetworks_erlang_fixed_point_unique
-- name    : KellyStochasticNetworks.erlang_fixed_point_unique
-- status  : Proved
-- author  : @naimengye
-- created : 2026-09-18T15:46:01.589126+00:00
-- url     : https://prove2.me/theorems/64648efd-281f-42ee-940b-240e5eca3add
-- title:
--   Theorem 3.20 — existence and uniqueness of the Erlang fixed point
-- statement:
--   Consider a loss network with $J$ links and $R$ routes: link $j$ carries $C_j \ge 1$ circuits, a
--   call on route $r$ requires $A_{jr}$ circuits from link $j$, and calls on route $r$ arrive at
--   rate $\nu_r > 0$. The **Erlang fixed point equations** are
--   $$E_j = E\!\left((1 - E_j)^{-1}\sum_r A_{jr}\,\nu_r\prod_i (1 - E_i)^{A_{ir}},\; C_j\right),
--     \qquad j = 1,\dots,J, \tag{3.7}$$
--   where $E(\nu,C)$ is Erlang's formula. Then there is **exactly one** vector
--   $(E_1,\dots,E_J) \in [0,1]^J$ satisfying them.
--
--   The equations are the reduced-load approximation: pretend the links block independently, so
--   that the traffic offered to link $j$ is the traffic on the routes through $j$, thinned by the
--   blocking probability of every other link each route uses, and then apply Erlang's formula link
--   by link. The factor $(1 - E_j)^{-1}$ removes link $j$'s own thinning from the product. This
--   approximation is what practitioners compute, and the theorem is what makes "the Erlang fixed
--   point" a well-formed phrase: repeated substitution, or a damped iteration, converges to a
--   vector that does not depend on where it started.
--
--   Existence is a short argument: the right-hand side defines a continuous map of the compact
--   convex cube $[0,1]^J$ into itself, so Brouwer's theorem applies. Uniqueness is the substance,
--   and the book obtains it by rewriting (3.7) as the stationary conditions of a strictly convex
--   minimization, the revised dual problem (3.8).
--
--   **Formalization Note** The incidence matrix has non-negative integer entries, which is the
--   general case of section 3.3 rather than only the $0$–$1$ case. The hypothesis $C_j \ge 1$ is
--   needed for the statement to mean anything: a link with no circuits has $E(\nu,0) = 1$
--   identically, and the factor $(1 - E_j)^{-1}$ would then be a division by zero. Under
--   $C_j \ge 1$ no solution has $E_j = 1$, so the quotient is taken at a non-zero denominator
--   throughout.
-- source:
--   Kelly & Yudovina, Stochastic Networks, CUP 2014, p. 67 (PDF p. 75), equation (3.7) and Theorem 3.20: 'Consider the equations E_j = E((1 - E_j)^{-1} sum_r A_{jr} nu_r prod_i (1 - E_i)^{A_{ir}}, C_j), j = 1, ..., J, (3.7) the generalization of the Erlang fixed point equations to matrices A that may not be 0-1. ... Theorem 3.20 There exists a unique solution (E_1, ..., E_J) in [0,1]^J satisfying the Erlang fixed point equations (3.7).' sha256 ec271d555059aee58613e5e9a98b8346214b16185c527314f5d94c1ac8b17b6a

import Mathlib
import Definitions.Def_KellyStochasticNetworks_Balance
import Definitions.Def_KellyStochasticNetworks_Erlang
import Definitions.Def_KellyStochasticNetworks_Migration
import Definitions.Def_KellyStochasticNetworks_LossNetwork

namespace KellyStochasticNetworks

theorem erlang_fixed_point_unique {J R : ℕ} (A : Fin J → Fin R → ℕ) (ν : Fin R → ℝ)
    (C : Fin J → ℕ) (hν : ∀ r, 0 < ν r) (hC : ∀ j, 1 ≤ C j) :
    ∃! E : Fin J → ℝ, (∀ j, E j ∈ Set.Icc (0 : ℝ) 1) ∧ ErlangFixedPoint A ν C E := by sorry

end KellyStochasticNetworks
