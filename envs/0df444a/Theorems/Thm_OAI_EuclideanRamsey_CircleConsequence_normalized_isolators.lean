-- Prove2me | Theorems.Thm_OAI_EuclideanRamsey_CircleConsequence_normalized_isolators
-- name    : OAI.EuclideanRamsey.CircleConsequence.normalized_isolators
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-19T12:27:22.736425+00:00
-- url     : https://prove2.me/theorems/fa87c1f7-ac45-4f65-80a9-c3fc89f05401
-- title:
--   A dual basis to the quadratic rows of five concyclic points
-- statement:
--   Let $a_0,\dots,a_4$ be five distinct points of $\mathbb R^2$ on a circle $|x-c|=r$, and let $K$ be the field generated over $\mathbb Q$ by their coordinates. With $\tilde a_i=(1,a_{i0},a_{i1})$, the quadratic row of $a_i$ is the vector $\bigl(\tilde a_i(p)\tilde a_i(q)\bigr)_{p,q\in\{0,1,2\}}\in K^9$. Then there are coefficient vectors $L_0,\dots,L_4\in K^9$ with
--   $$
--   \sum_{p,q}L_i(p,q)\,q_j(p,q)=\delta_{ij}\qquad(0\le i,j\le4).
--   $$
--
--   So the quadratic rows of the five points admit a dual system over $K$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/EuclideanRamsey/CircleRows.lean#L12-L34

import Mathlib
import Definitions.Def_EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_Model__EuclideanRamseyCircle
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleInterpolation
import Definitions.Def_OAI_Combinatorics_EuclideanRamsey_CircleRows

open OAI OAI.EuclideanRamsey OAI.EuclideanRamsey.CircleConsequence

theorem OAI.EuclideanRamsey.CircleConsequence.normalized_isolators (a : Fin 5 → Space 2) (ha : Function.Injective a)
    (c : Space 2) (r : ℝ) (hc : ∀ i, dist (a i) c = r) :
    ∃ L : Fin 5 → QIndex → Coeff a,
      ∀ i j, ∑ q, L i q * quadraticRow a j q = if j = i then 1 else 0 := by sorry
