-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_circle_five_rows_independent
-- name    : OAI.EuclideanRamsey.CircleConsequence.circle_five_rows_independent
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:27:52.685145+00:00
-- url     : https://prove2.me/theorems/5bce7932-710c-4ba0-87c6-a7a7508d5d9e
-- title:
--   The quadratic rows of five concyclic points are independent
-- statement:
--   Let $a_0,\dots,a_4$ be five distinct points of $\mathbb R^2$ on a circle $|x-c|=r$, and let $K$ be the field generated over $\mathbb Q$ by their coordinates. With $\tilde a_i=(1,a_{i0},a_{i1})$, the quadratic row of $a_i$ is the vector $\bigl(\tilde a_i(p)\tilde a_i(q)\bigr)_{p,q\in\{0,1,2\}}\in K^9$. Then the five quadratic rows are linearly independent over $K$:
--   $$
--   \sum_{j=0}^4g_j\,q_j=0\ \Longrightarrow\ g_0=\dots=g_4=0 .
--   $$
--
--   This is the quadratic independence hypothesis of the sufficient condition for Ramsey configurations, verified for five points on a circle.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CircleRows.lean#L52-L78

import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows

open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence

theorem OAI.EuclideanRamsey.CircleConsequence.circle_five_rows_independent (a : Fin 5 → Space 2)
    (ha : Function.Injective a) (c : Space 2) (r : ℝ)
    (hc : ∀ i, dist (a i) c = r) :
    LinearIndependent (Coeff a) (fun i : Fin 5 => fun q : QIndex =>
      augmented a i q.1 * augmented a i q.2) := by sorry
