-- Prove2me | Theorems.Thm_NashVecOpt_SharedConstraint_order_characterization
-- name    : NashVecOpt.SharedConstraint.order_characterization
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-21T05:06:02.322561+00:00
-- url     : https://prove2.me/theorems/c39c1cb7-93d0-464f-818f-9972da92b15d
-- title:
--   §2.2, p. 7 — comparisons under the player and full cones
-- statement:
--   Let $x,\bar x$ be any two joint strategies in an $N$-player game, $N\ge2$. For each player $i$, the augmented outcomes satisfy
--
--   $$(x,f(x))\ge_{C_i}(\bar x,f(\bar x))
--     \quad\Longleftrightarrow\quad
--     x_{-i}=\bar x_{-i}\ \text{and}\ f_i(x)\ge f_i(\bar x).$$
--
--   The corresponding comparison under $C$ holds exactly when the comparison holds under at least one $C_i$. This makes the unilateral meaning of the ordering relation explicit.
--
--   **Formalization Note** The paper's $\ge_K$ is written using `coneLE K` with the arguments reversed. No feasibility assumption on $x$ or $\bar x$ is made in the source paragraph. The cardinality hypothesis records the paper's standing $N\ge2$ but is not needed for this algebraic characterization.
-- source:
--   Feinstein, Rudloff, Characterizing and Computing the Set of Nash Equilibria via Vector Optimization, arXiv:2109.14932v5, p. 7, §2.2, paragraph beginning 'Let us first study the cone C_i'

import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Model

namespace NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- §2.2, p. 7, paragraph before Theorem 2.6: player-cone comparison fixes the other
strategies, and full-cone comparison is comparison for some player. -/
theorem order_characterization (hN : 2 ≤ Fintype.card ι)
    (f : ι → (∀ j, E j) → ℝ) (x xbar : ∀ j, E j) :
    (∀ i, coneLE (coneI (E := E) i) (obj f xbar) (obj f x) ↔
      (∀ j, j ≠ i → x j = xbar j) ∧ f i xbar ≤ f i x) ∧
    (coneLE (orderCone (E := E)) (obj f xbar) (obj f x) ↔
      ∃ i, coneLE (coneI (E := E) i) (obj f xbar) (obj f x)) := by sorry

end NashVecOpt.SharedConstraint
