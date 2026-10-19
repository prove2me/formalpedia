-- Prove2me | Theorems.Thm_HyperKCut_Structure_theorem_3_1
-- name    : HyperKCut.Structure.theorem_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:21.374159+00:00
-- url     : https://prove2.me/theorems/f76a33f6-d413-4730-9e88-d75dca0bc54f
-- title:
--   Theorem 3.1 — uncrossing theorem for hypergraph k-cut
-- statement:
--   Let $k\ge2$, $\emptyset\ne R\subsetneq U\subsetneq V$, and $S=\{u_1,\ldots,u_p\}\subseteq U\setminus R$ have $p\ge2k-2$ distinct vertices. For each $i$, let $(V\setminus A_i,A_i)$ be a minimum $((S\cup R)\setminus\{u_i\},V\setminus U)$-terminal cut, with $u_i\in A_i$ and $u_i\notin A_j$ for $j\ne i$. Then there is a $k$-partition $(P_1,\ldots,P_k)$ such that $V\setminus U\subsetneq P_k$ and
--
--   $$2\operatorname{cost}(P_1,\ldots,P_k)\le d(A_i)+d(A_j)\quad\text{for all distinct }i,j.$$
--
--   This is the paper's principal uncrossing theorem, used to establish the structural target.
--
--   **Formalization Note** The factor-two inequality is the exact natural-number form of the paper's half-minimum bound. The final part is strictly larger than $V\setminus U$.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 7 (PDF 8), Theorem 3.1 (restated p. 14, PDF 15)

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Theorem 3.1, p. 7: the uncrossing theorem for hypergraph k-cut. -/
theorem theorem_3_1 (H : Hypergraph V) (k p : ℕ)
    (hk : 2 ≤ k) (hp : 2 * k - 2 ≤ p)
    (R U : Finset V) (hR : R.Nonempty) (hRU : R ⊂ U)
    (hUV : U ⊂ (Finset.univ : Finset V))
    (u : Fin p → V) (huinj : Function.Injective u)
    (hu : ∀ i, u i ∈ U \ R)
    (A : Fin p → Finset V)
    (hA : ∀ i, IsMinTerminalCut H
      (((Finset.univ.image u) ∪ R).erase (u i)) Uᶜ (A i)ᶜ)
    (hui : ∀ i, u i ∈ A i)
    (huj : ∀ i j, i ≠ j → u i ∉ A j) :
    ∃ P : Fin k → Finset V, IsPartition P ∧
      Uᶜ ⊂ P ⟨k - 1, by omega⟩ ∧
      ∀ i j : Fin p, i ≠ j → 2 * cost H P ≤ d H (A i) + d H (A j) := by sorry

end HyperKCut.Structure
