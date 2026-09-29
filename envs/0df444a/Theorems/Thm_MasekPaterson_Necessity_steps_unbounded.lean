-- Prove2me | Theorems.Thm_MasekPaterson_Necessity_steps_unbounded
-- name    : MasekPaterson.Necessity.steps_unbounded
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:22:55.229311+00:00
-- url     : https://prove2.me/theorems/fd8daca7-8e81-4270-8745-9e93e990737e
-- title:
--   Theorem 5 — with costs 1 and π the steps δ_{k,k+1} − δ_{k,k} are pairwise distinct, so the set of possible steps is infinite
-- statement:
--   Let $\gamma$ be the cost function and $A, B$ the infinite strings of the §4.1 example over $\Sigma = \{a, b, c\}$ (replacement costs $0$, $1$ and $\pi$, insertions and deletions $5$), and $\delta_{i,j} = \delta(\gamma, A^i, B^j)$. Then:
--
--   1. the horizontal steps $\delta_{k,k+1} - \delta_{k,k}$, for $k = 0, 1, 2, \dots$, are pairwise distinct: $$\delta_{k,k+1} - \delta_{k,k} = \delta_{k',k'+1} - \delta_{k',k'} \implies k = k';$$
--   2. the set of possible steps of $\gamma$ (all differences of adjacent entries of the edit matrices of all pairs of strings over $\Sigma$) is infinite.
--
--   Part 1 shows that the edit matrix of $A^n$ and $B^n$ already contains at least $n$ different steps, so the number of distinct steps grows linearly with the string length. Part 2 is the direct contrast with the paper's Lemma 4, which shows that the set of possible steps is finite whenever the alphabet is finite and the cost set is discrete; the example meets every other condition of the paper, so discreteness cannot be dropped.
--
--   **Formalization Note** The paper states Theorem 5 about the running time of Algorithm Y ("Discreteness is a necessary condition for Algorithm Y to run in time $O(k^m)$ on length $m$ strings and step sequences"); its proof establishes that the number of distinct steps grows linearly with the string length, which is what is stated here. Running time is not formalized.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 30, Theorem 5 and its proof

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
import Definitions.Def_MasekPaterson_Necessity_example
import Definitions.Def_MasekPaterson_Shared_steps
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- Theorem 5, pinned to what its proof establishes: in the example, the horizontal steps
`δ_{k,k+1} - δ_{k,k}` (`k = 0, 1, 2, …`) are pairwise distinct, so the edit matrix of
`A^n, B^n` has at least `n` distinct steps, and the set of possible steps of the cost
function is infinite. -/
theorem steps_unbounded :
    Function.Injective (fun k : ℕ => exDelta k (k + 1) - exDelta k k) ∧
    ¬ (possibleSteps exCost).Finite := by sorry

end MasekPaterson.Necessity
