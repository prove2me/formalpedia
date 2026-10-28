-- Prove2me | Theorems.Thm_NashVecOpt_SharedConstraint_theorem_2_6
-- name    : NashVecOpt.SharedConstraint.theorem_2_6
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:05.114245+00:00
-- url     : https://prove2.me/theorems/c20fbe86-3a8f-4a3a-b85f-0fe4b7f31543
-- title:
--   Theorem 2.6, p. 7 — Nash equilibria equal the C-minimizers
-- statement:
--   For an $N$-player shared-constraint game with $N\ge2$, let $f_i$ be arbitrary real-valued cost functions, $\mathbb X$ any shared feasible set of joint strategies, $g(x)=(x,f(x))$, and $C$ the ordering cone of equation (6). The whole Nash equilibrium set is exactly the vector minimizer set:
--
--   $$\mathrm{NE}(f,\mathbb X)
--     =C\text{-argmin}\{(x,f(x)):x\in\mathbb X\}.$$
--
--   The equality applies without regularity, convexity, or existence assumptions and can therefore describe an empty equilibrium set or one with many points.
--
--   **Formalization Note** A joint strategy is a dependent function over a finite player type; its $i$th unilateral deviation is `Function.update`. The shared feasible set is never replaced by a product set. The $N\ge2$ hypothesis reproduces the paper's standing model assumption, although the equality itself does not need it.
-- source:
--   Feinstein, Rudloff, Characterizing and Computing the Set of Nash Equilibria via Vector Optimization, arXiv:2109.14932v5, p. 7, Theorem 2.6

import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Model

namespace NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Theorem 2.6, p. 7: the Nash equilibria of a shared-constraint game are exactly the
Pareto minimizers of its augmented objective under cone (6). -/
theorem theorem_2_6 (hN : 2 ≤ Fintype.card ι) (f : ι → (∀ j, E j) → ℝ)
    (X : Set (∀ j, E j)) :
    NE f X = vArgMin (orderCone (E := E)) (obj f) X := by sorry

end NashVecOpt.SharedConstraint
