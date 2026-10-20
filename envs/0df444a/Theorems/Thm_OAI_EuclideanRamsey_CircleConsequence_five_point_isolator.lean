-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_five_point_isolator
-- name    : OAI.EuclideanRamsey.CircleConsequence.five_point_isolator
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:26:53.365431+00:00
-- url     : https://prove2.me/theorems/659f822f-2fe0-4ff8-98eb-351a6df7f76a
-- title:
--   A quadric through four of five concyclic points that misses the fifth
-- statement:
--   Let $a_0,\dots,a_4$ be five distinct points of $\mathbb R^2$ on a circle $|x-c|=r$, and let $K$ be the field generated over $\mathbb Q$ by their coordinates. With $\tilde a_i=(1,a_{i0},a_{i1})$, the quadratic row of $a_i$ is the vector $\bigl(\tilde a_i(p)\tilde a_i(q)\bigr)_{p,q\in\{0,1,2\}}\in K^9$. Write the circle as $|x-c|^2=R$. For any labelling $e$ of the five points, there is a $3\times3$ matrix $M$ over $K$ with
--   $$
--   \tilde a_m^{\mathsf T}M\tilde a_m=0\ \ (m\ne e(0)),\qquad\tilde a_{e(0)}^{\mathsf T}M\tilde a_{e(0)}\ne0 .
--   $$
--
--   Such isolators show that the five quadratic rows are linearly independent.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CircleInterpolation.lean#L72-L94

import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation

open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence

theorem OAI.EuclideanRamsey.CircleConsequence.five_point_isolator (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (R : ℝ)
    (hc : ∀ m, (a m 0-c 0)^2 + (a m 1-c 1)^2 = R)
    (e : Equiv.Perm (Fin 5)) :
    ∃ M : Matrix (Option (Fin 2)) (Option (Fin 2)) (Coeff a),
      (∀ m, m ≠ e 0 →
        (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
          M α β * augmented a m α * augmented a m β) = 0) ∧
      (∑ α : Option (Fin 2), ∑ β : Option (Fin 2),
          M α β * augmented a (e 0) α * augmented a (e 0) β) ≠ 0 := by sorry
