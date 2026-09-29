-- Prove2me | Theorems.Thm_OnlinePrimalDual_Framework_algorithm1_competitive_ratio
-- name    : OnlinePrimalDual.Framework.algorithm1_competitive_ratio
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-21T05:35:56.776956+00:00
-- url     : https://prove2.me/theorems/548d05f9-43b3-4aed-a30b-b952378007d2
-- title:
--   Theorem 4.1 — Algorithm 1's competitive ratio
-- statement:
--   Let `ord : List J` be the online arrival order of the constraints (a permutation of `J`) and
--   `t : J → ℕ` the number of inner-loop increments Algorithm 1 performs while processing each
--   constraint (so `y_j := t_j` is its integral dual/packing value and `alg1X inst ord t` its own
--   primal/covering value), assume `c_i ≥ 1` for all `i` (the book's standing hypothesis for this
--   algorithm, p. 118) and that the resulting covering solution is feasible
--   (`∀j, ∑_{i∈S(j)} x_i ≥ 1`, i.e. the run has completed). Then: (i) the integral packing
--   solution `t` violates each dual constraint by a factor of at most `log₂(3d+1)`; (ii) the
--   covering solution is `2·log₂(3d+1)`-competitive against any feasible offline covering
--   solution; (iii) the integral packing solution is `2`-competitive against any feasible offline
--   packing solution.
-- source:
--   Buchbinder & Naor, The Design of Competitive Online Algorithms via a Primal-Dual Approach, FnT TCS 2009, p. 118-120, Theorem 4.1

import Mathlib
import Definitions.Def_OnlinePrimalDual_Framework_CoveringInstance
import Definitions.Def_OnlinePrimalDual_Framework_dualSum
import Definitions.Def_OnlinePrimalDual_Framework_alg1X

namespace OnlinePrimalDual.Framework

/-- **Theorem 4.1** (p. 118, PDF p. 29), Algorithm 1, the basic discrete algorithm. `ord` is the
online arrival order of the constraints (`hord_nodup`/`hord_mem`: a permutation of `J`), and `t j`
is the number of inner-loop increments the algorithm performs while processing constraint `j`;
the resulting integral dual/packing values are `(t j : ℝ)`, and the resulting primal values are
Algorithm 1's own final output `alg1X inst ord t` (p. 118, step (1a) applied verbatim, no
round-uniform substitution — see `Def_OnlinePrimalDual_Framework_alg1X`). `hc1` is the book's
standing assumption `cᵢ ≥ 1` for this algorithm (p. 118). `h_feasible` is the book's Claim (1)
that the algorithm produces a primal-feasible covering solution, taken here as the hypothesis
characterizing a completed run (the online update rule only ever increases `t j` until this
holds, p. 118), stated about the algorithm's real output `alg1X inst ord t`. The three
conclusions are the book's own three bullets, stated via weak duality against an arbitrary
offline-feasible comparison solution rather than against an unconstructed LP optimum: (i) the
integral packing solution `t` violates each dual constraint by a factor of at most `log₂(3d+1)`
(Claims (2)-(3) combined with the proof's own displayed bound, p. 120); (ii) the covering solution
`alg1X inst ord t` is `2·log₂(3d+1)`-competitive against any feasible offline covering solution;
(iii) the integral packing solution `t` is `2`-competitive against any feasible offline packing
solution (Claim (2), `P ≤ 2D`, combined with weak duality both ways:
`OPTpacking ≤ OPTcovering ≤ P ≤ 2D`). -/
theorem algorithm1_competitive_ratio {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I]
    [DecidableEq J] (inst : CoveringInstance I J) (hc1 : ∀ i, 1 ≤ inst.c i) (ord : List J)
    (hord_nodup : ord.Nodup) (hord_mem : ∀ j, j ∈ ord) (t : J → ℕ)
    (h_feasible : ∀ j, 1 ≤ ∑ i ∈ inst.S j, alg1X inst ord t i) :
    (∀ i : I, (∑ j ∈ Finset.univ.filter (fun j => i ∈ inst.S j), (t j : ℝ)) ≤
        inst.c i * Real.logb 2 (3 * inst.d + 1)) ∧
    (∀ x'' : I → ℝ, (∀ i, 0 ≤ x'' i) → (∀ j, 1 ≤ ∑ i ∈ inst.S j, x'' i) →
        ∑ i, inst.c i * alg1X inst ord t i ≤
          2 * Real.logb 2 (3 * inst.d + 1) * ∑ i, inst.c i * x'' i) ∧
    (∀ y'' : J → ℝ, (∀ j, 0 ≤ y'' j) → (∀ i, dualSum inst y'' i ≤ inst.c i) →
        ∑ j, y'' j ≤ 2 * ∑ j, (t j : ℝ)) := by sorry

end OnlinePrimalDual.Framework
