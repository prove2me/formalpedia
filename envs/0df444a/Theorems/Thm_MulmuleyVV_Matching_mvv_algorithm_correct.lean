-- Prove2me | Theorems.Thm_MulmuleyVV_Matching_mvv_algorithm_correct
-- name    : MulmuleyVV.Matching.mvv_algorithm_correct
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T16:38:33.857489+00:00
-- url     : https://prove2.me/theorems/8ce65325-63ce-4dc5-a041-436a8e32a1de
-- title:
--   Steps 1–3 of the MVV algorithm output a minimum weight perfect matching with probability at least 1/2
-- statement:
--   Let $G$ be a graph on the vertices $v_1, \dots, v_n$ with edge set $E$, $m = |E|$, and suppose $G$ has a perfect matching. Assign to each edge an integer weight $w_{ij}$ chosen uniformly and independently from $\{1, 2, \dots, 2m\}$, form the integer matrix $B$ from the Tutte matrix of $G$ by substituting $x_{ij} = 2^{w_{ij}}$, and run the algorithm of §4:
--
--   1. Step 1: compute $|B|$ and obtain $w$, where $2^{2w}$ is the highest power of 2 dividing $|B|$;
--   2. Step 2: compute $\operatorname{adj}(B)$, whose $(j,i)$ entry gives the minor $|B_{ij}|$;
--   3. Step 3: for each edge $(v_i, v_j)$, include it in the output if $|B_{ij}|\,2^{w_{ij}}/2^{2w}$ is odd.
--
--   Then
--
--   $$
--   \Pr\bigl[\text{the output is a perfect matching of } G \text{ of minimum weight}\bigr] \ \ge\ \frac12 .
--   $$
--
--   This is the correctness half of the paper's main Theorem (p. 109): the algorithm, whose only nontrivial work is one determinant and one adjugate of an integer matrix, finds a perfect matching, and in fact picks out the minimum weight perfect matching whenever the random weights isolate it.
--
--   **Formalization Note** The sample space is `Fintype.piFinset (fun _ : G.edgeSet => Finset.Icc 1 (2m))` and the bound is $(2m)^m \le 2\cdot\#\{w : \dots\}$. The output `mvvOutput G w` is computed only from $B$, $|B|$, $\operatorname{adj}(B)$, the 2-adic valuation and parity; it does not refer to matchings. "Of minimum weight" means its weight is at most that of every perfect matching. The complexity half of the Theorem (RNC², $O(n^{3.5}m)$ processors) is not formalized. The hypothesis that $G$ has a perfect matching is the paper's (input of §4).
-- source:
--   Mulmuley, Vazirani, Vazirani, Matching is as easy as matrix inversion, Combinatorica 7 (1987), p. 108 (§4, 'Our parallel algorithm will pick out this perfect matching') and p. 109 (Steps 1–3 and the correctness half of the Theorem)

import Mathlib
import Definitions.Def_MulmuleyVV_Matching_SetSystem
import Definitions.Def_MulmuleyVV_Matching_Algorithm

namespace MulmuleyVV.Matching

open Classical in
theorem mvv_algorithm_correct {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : ∃ M : Finset G.edgeSet, IsPerfectMatchingEdges G M) :
    (2 * Fintype.card G.edgeSet) ^ Fintype.card G.edgeSet ≤
      2 * ((Fintype.piFinset fun _ : G.edgeSet => Finset.Icc 1 (2 * Fintype.card G.edgeSet)).filter
        (fun w => IsPerfectMatchingEdges G (mvvOutput G w) ∧
          ∀ M' : Finset G.edgeSet, IsPerfectMatchingEdges G M' →
            setWeight w (mvvOutput G w) ≤ setWeight w M')).card := by sorry

end MulmuleyVV.Matching
