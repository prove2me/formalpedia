-- Prove2me | Theorems.Thm_MulmuleyVV_Matching_lemma2_det_two_adic
-- name    : MulmuleyVV.Matching.lemma2_det_two_adic
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:36:52.62269+00:00
-- url     : https://prove2.me/theorems/53d9df84-77be-45e3-bf2b-f7db7736a9d1
-- title:
--   Lemma 2 — if the minimum weight perfect matching is unique, of weight $w$, then $|B| \ne 0$ and $2^{2w}$ is the highest power of 2 dividing $|B|$
-- statement:
--   Let $G$ be a graph with vertices $v_1, \dots, v_n$ and edge weights $w_{ij} \in \mathbb{N}$, and let $B$ be the integer matrix obtained from the Tutte matrix of $G$ by substituting $x_{ij} = 2^{w_{ij}}$. Suppose the minimum weight perfect matching $M$ of $G$ is unique, and let $w$ be its weight. Then
--
--   $$
--   |B| \neq 0, \qquad 2^{2w} \mid |B|, \qquad 2^{2w+1} \nmid |B| ,
--   $$
--
--   that is, the highest power of $2$ dividing $|B|$ is $2^{2w}$.
--
--   Thus evaluating one integer determinant reveals the weight of the minimum weight perfect matching once that matching is isolated.
--
--   **Formalization Note** Weights are arbitrary natural numbers here (no range restriction). "The minimum weight perfect matching is unique" is stated as: $M$ is a perfect matching and every other perfect matching has strictly larger weight.
-- source:
--   Mulmuley, Vazirani, Vazirani, Matching is as easy as matrix inversion, Combinatorica 7 (1987), p. 108, Lemma 2

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_SetSystem
import Definitions.Def_MulmuleyVV_Matching_Algorithm

namespace MulmuleyVV.Matching

theorem lemma2_det_two_adic {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : G.edgeSet → ℕ) (M : Finset G.edgeSet) (hM : IsPerfectMatchingEdges G M)
    (huniq : ∀ M' : Finset G.edgeSet, IsPerfectMatchingEdges G M' → M' ≠ M →
      setWeight w M < setWeight w M') :
    (weightedTutteMatrix G w).det ≠ 0 ∧
      (2 : ℤ) ^ (2 * setWeight w M) ∣ (weightedTutteMatrix G w).det ∧
      ¬ (2 : ℤ) ^ (2 * setWeight w M + 1) ∣ (weightedTutteMatrix G w).det := by sorry

end MulmuleyVV.Matching
