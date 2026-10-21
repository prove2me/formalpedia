-- Prove2me | Theorems.Thm_NashVecOpt_SharedConstraint_cone_decomposition
-- name    : NashVecOpt.SharedConstraint.cone_decomposition
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:03.268829+00:00
-- url     : https://prove2.me/theorems/17e91228-8ba6-405e-a730-794667bf727a
-- title:
--   §2.2, p. 6 — decomposition into convex player cones
-- statement:
--   In an $N$-player shared-constraint game with $N\ge2$, let $C$ and $C_i$ be the ordering cones in equations (6) and (7). Then
--
--   $$C=\bigcup_{i=1}^{N}C_i,$$
--
--   and every $C_i$ is convex and closed under multiplication by any nonnegative real scalar. This identifies the convex pieces of the paper's possibly nonconvex comparison cone.
--
--   **Formalization Note** The player set is an arbitrary finite type of cardinality at least two. The cardinality assumption carries the paper's standing convention; the cone identity itself does not use it. Convexity is Mathlib's `Convex ℝ`, and nonnegative scaling is stated explicitly.
-- source:
--   Feinstein, Rudloff, Characterizing and Computing the Set of Nash Equilibria via Vector Optimization, arXiv:2109.14932v5, p. 6, §2.2, equations (6)–(7), paragraph beginning 'Though the ordering cone C is not convex'

import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Model

namespace NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- §2.2, p. 6, (6)–(7): the ordering cone is the union of the player cones, each convex
and closed under nonnegative scaling. -/
theorem cone_decomposition (hN : 2 ≤ Fintype.card ι) :
    ((orderCone : Set ((∀ j, E j) × (ι → ℝ))) = ⋃ i, coneI i) ∧
    ∀ i, Convex ℝ (coneI (E := E) i) ∧
      ∀ c : ℝ, 0 ≤ c → ∀ z ∈ coneI (E := E) i, c • z ∈ coneI (E := E) i := by sorry

end NashVecOpt.SharedConstraint
