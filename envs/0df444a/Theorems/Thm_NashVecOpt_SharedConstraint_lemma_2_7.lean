-- Prove2me | Theorems.Thm_NashVecOpt_SharedConstraint_lemma_2_7
-- name    : NashVecOpt.SharedConstraint.lemma_2_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T05:05:59.055226+00:00
-- url     : https://prove2.me/theorems/9b97caba-4a4c-4f28-8ee3-1f41ae501f58
-- title:
--   Lemma 2.7, p. 7 — decomposition of the minimizer set
-- statement:
--   Let $f$ be the arbitrary cost profile and $\mathbb X$ the arbitrary shared feasible set of an $N$-player game with $N\ge2$. With the augmented objective $g(x)=(x,f(x))$, the full-cone minimizers equal the intersection of the player-cone minimizers:
--
--   $$C\text{-argmin}\{(x,f(x)):x\in\mathbb X\}
--     =\bigcap_{i=1}^{N}C_i\text{-argmin}\{(x,f(x)):x\in\mathbb X\}.$$
--
--   This is the paper's decomposition of the entire Pareto minimizer set, including when the feasible set is empty.
--
--   **Formalization Note** The cones are exactly (6) and (7), and the minimizer notion is Definition 2.3. The stated $N\ge2$ is the paper's standing convention; the identity can be proved without using it.
-- source:
--   Feinstein, Rudloff, Characterizing and Computing the Set of Nash Equilibria via Vector Optimization, arXiv:2109.14932v5, p. 7, Lemma 2.7

import Mathlib
import Definitions.Def_NashVecOpt_SharedConstraint_Model

namespace NashVecOpt.SharedConstraint

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {E : ι → Type} [∀ i, AddCommGroup (E i)] [∀ i, Module ℝ (E i)]

/-- Lemma 2.7, p. 7: the full-cone minimizers equal the intersection of the player-cone
minimizers. -/
theorem lemma_2_7 (hN : 2 ≤ Fintype.card ι) (f : ι → (∀ j, E j) → ℝ)
    (X : Set (∀ j, E j)) :
    vArgMin (orderCone (E := E)) (obj f) X =
      ⋂ i, vArgMin (coneI (E := E) i) (obj f) X := by sorry

end NashVecOpt.SharedConstraint
