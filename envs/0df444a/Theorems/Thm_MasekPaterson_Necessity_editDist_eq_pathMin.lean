-- Prove2me | Theorems.Thm_MasekPaterson_Necessity_editDist_eq_pathMin
-- name    : MasekPaterson.Necessity.editDist_eq_pathMin
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T21:19:56.779995+00:00
-- url     : https://prove2.me/theorems/4760ed43-d18c-44a2-b392-a8f8b2afc9fa
-- title:
--   §2.3 — for a normalized cost function, δ_{i,j} is the minimum cost of an edit path from (0, 0) to (i, j)
-- statement:
--   Let $\gamma$ be a cost function assigning a nonnegative real number to every edit operation, normalized as in §1.1: $\gamma(a \to b) = \delta(\gamma, a, b)$ for every edit operation $a \to b$. Let $A = A_1 A_2 \cdots$ and $B = B_1 B_2 \cdots$ be strings over the alphabet, with prefixes $A^i = A_1 \cdots A_i$, $B^j = B_1 \cdots B_j$ and edit matrix $\delta_{i,j} = \delta(\gamma, A^i, B^j)$. An edit path from $(0,0)$ to $(i,j)$ is a sequence of moves through the matrix, each increasing $i$, $j$, or both by $1$: the move $(p,q) \to (p+1,q)$ deletes $A_{p+1}$ at cost $D_{A_{p+1}}$, the move $(p,q) \to (p,q+1)$ inserts $B_{q+1}$ at cost $I_{B_{q+1}}$, and the move $(p,q) \to (p+1,q+1)$ replaces $A_{p+1}$ by $B_{q+1}$ at cost $R_{A_{p+1},B_{q+1}}$. Then for all $i, j \ge 0$,
--
--   $$\delta_{i,j} = \min\{\text{cost of an edit path from } (0, 0) \text{ to } (i, j)\}.$$
--
--   In words: to transform $A^i$ into $B^j$ it is enough to consider edit sequences that proceed left to right through the two strings, which are exactly the edit paths through the matrix. This identifies the edit distance, defined as a minimum over arbitrary edit sequences, with the path costs that §4 compares.
--
--   **Formalization Note** The strings are given as 1-based infinite sequences $\mathbb N \to \alpha$ whose prefixes are $A^i$, $B^j$ (every finite string over a nonempty alphabet is such a prefix). The nonnegativity of $\gamma$ and the normalization $\gamma(a \to b) = \delta(\gamma, a, b)$ are the standing assumptions of §1.1 (p. 19), stated as hypotheses. The paper's assumption $|A| \ge |B|$ is not used.
-- source:
--   Masek, Paterson, A Faster Algorithm Computing String Edit Distances, J. Comput. System Sci. 20, 1980, p. 24, Section 2.3 (Edit Paths); standing assumptions p. 19, Section 1.1

import Mathlib
import Definitions.Def_MasekPaterson_Shared_editDist
import Definitions.Def_MasekPaterson_Necessity_editPaths
open MasekPaterson.Shared

namespace MasekPaterson.Necessity

/-- §2.3: for a nonnegative normalized cost function `γ` (`γ(a → b) = δ(γ, a, b)`, §1.1) and
any strings `A, B` (given as 1-based sequences, `A^i = A_1 ⋯ A_i`), every edit matrix entry
`δ_{i,j} = δ(γ, A^i, B^j)` is the minimum cost of an edit path from `(0, 0)` to `(i, j)`. -/
theorem editDist_eq_pathMin {α : Type*} (γ : EditOp α → ℝ) (hγ : ∀ o, 0 ≤ γ o)
    (hnorm : IsNormalized γ) (A B : ℕ → α) (i j : ℕ) :
    editDist γ (List.ofFn fun t : Fin i => A (t.val + 1))
        (List.ofFn fun t : Fin j => B (t.val + 1)) =
      pathMin γ A B (0, 0) (i, j) := by sorry

end MasekPaterson.Necessity
