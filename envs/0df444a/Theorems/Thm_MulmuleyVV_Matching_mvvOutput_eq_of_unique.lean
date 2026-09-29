-- Prove2me | Theorems.Thm_MulmuleyVV_Matching_mvvOutput_eq_of_unique
-- name    : MulmuleyVV.Matching.mvvOutput_eq_of_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T16:38:08.892414+00:00
-- url     : https://prove2.me/theorems/44f1044a-4d20-4789-b9ef-84fb4e7c9dc5
-- title:
--   §4, Steps 1–3 — when the minimum weight perfect matching $M$ is unique, Step 1 obtains its weight and Steps 2–3 output $M$
-- statement:
--   Let $G$ be a graph with vertices $v_1, \dots, v_n$, edge weights $w_{ij} \in \mathbb{N}$, and let $B$ be the matrix obtained from its Tutte matrix by substituting $x_{ij} = 2^{w_{ij}}$. Suppose the minimum weight perfect matching $M$ of $G$ is unique. Then the algorithm of §4
--
--   1. Step 1: compute $|B|$ and obtain $w$ (the exponent for which $2^{2w}$ is the highest power of 2 dividing $|B|$);
--   2. Step 2: compute $\operatorname{adj}(B)$, whose $(j,i)$ entry gives the minor $|B_{ij}|$;
--   3. Step 3: for each edge $(v_i, v_j)$, include it if $|B_{ij}|\,2^{w_{ij}}/2^{2w}$ is odd,
--
--   obtains in Step 1 exactly the weight of $M$, and outputs
--
--   $$
--   \{\text{edges selected in Step 3}\} \;=\; M .
--   $$
--
--   This is the deterministic core of the algorithm's correctness: once the weights isolate a minimum weight perfect matching, Steps 1–3 find it.
--
--   **Formalization Note** Step 1's $w$ is `step1Weight G w` $= \lfloor \nu_2(|B|)/2 \rfloor$ and the output is `mvvOutput G w` (both from the definition file); weights are arbitrary natural numbers.
-- source:
--   Mulmuley, Vazirani, Vazirani, Matching is as easy as matrix inversion, Combinatorica 7 (1987), p. 109, §4, Steps 1–3 (with Lemmas 2 and 3)

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_SetSystem
import Definitions.Def_MulmuleyVV_Matching_Algorithm

namespace MulmuleyVV.Matching

theorem mvvOutput_eq_of_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : G.edgeSet → ℕ) (M : Finset G.edgeSet) (hM : IsPerfectMatchingEdges G M)
    (huniq : ∀ M' : Finset G.edgeSet, IsPerfectMatchingEdges G M' → M' ≠ M →
      setWeight w M < setWeight w M') :
    step1Weight G w = setWeight w M ∧ mvvOutput G w = M := by sorry

end MulmuleyVV.Matching
