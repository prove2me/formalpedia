-- Prove2me | Theorems.Thm_HyperKCut_Structure_lemma_3_2
-- name    : HyperKCut.Structure.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T04:18:10.261511+00:00
-- url     : https://prove2.me/theorems/a35255b3-68a1-49a7-bfc0-16997a67ea80
-- title:
--   Lemma 3.2 — a low-σ partition from minimum terminal cuts
-- statement:
--   Let $\emptyset\ne R\subsetneq U\subsetneq V$, and let $S=\{u_1,\ldots,u_p\}\subseteq U\setminus R$ contain $p\ge2$ distinct vertices. For each $i$, suppose $(V\setminus A_i,A_i)$ is a minimum $((S\cup R)\setminus\{u_i\},V\setminus U)$-terminal cut and that $u_i\in A_i$ but $u_i\notin A_j$ for $j\ne i$. Define $Z=\bigcap_i(V\setminus A_i)$, $W=\bigcup_{i<j}(A_i\cap A_j)$, and $Y_i=A_i\setminus W$. Then $(Y_1,\ldots,Y_p,W,Z)$ is a partition and
--
--   $$\sigma(Y_1,\ldots,Y_p,W,Z)\le d(A_i)+d(A_j)\quad\text{for every }i\ne j.$$
--
--   This is the uncrossing estimate feeding Theorem 3.1.
--
--   **Formalization Note** The $u_i$ are represented by an injective map. The source set of the terminal cut is $V\setminus A_i$, not $A_i$.
-- source:
--   Chandrasekaran & Chekuri, Hypergraph k-cut for fixed k in deterministic polynomial time, arXiv:2009.12442v1, p. 13 (PDF 14), Lemma 3.2

import Mathlib
import Definitions.Def_HyperKCut_Structure_Model

namespace HyperKCut.Structure

variable {V : Type} [Fintype V] [DecidableEq V]

/-- Lemma 3.2, p. 13: uncrossing minimum terminal cuts into a low-sigma partition. -/
theorem lemma_3_2 (H : Hypergraph V) (p : ℕ) (hp : 2 ≤ p)
    (R U : Finset V) (hR : R.Nonempty) (hRU : R ⊂ U)
    (hUV : U ⊂ (Finset.univ : Finset V))
    (u : Fin p → V) (huinj : Function.Injective u)
    (hu : ∀ i, u i ∈ U \ R)
    (A : Fin p → Finset V)
    (hA : ∀ i, IsMinTerminalCut H
      (((Finset.univ.image u) ∪ R).erase (u i)) Uᶜ (A i)ᶜ)
    (hui : ∀ i, u i ∈ A i)
    (huj : ∀ i j, i ≠ j → u i ∉ A j) :
    let Z : Finset V := Finset.univ.filter (fun v => ∀ i, v ∉ A i)
    let W : Finset V := Finset.univ.filter
      (fun v => ∃ i j : Fin p, i ≠ j ∧ v ∈ A i ∧ v ∈ A j)
    let Y : Fin p → Finset V := fun i => A i \ W
    IsPartitionYWZ Y W Z ∧
      ∀ i j : Fin p, i ≠ j → sigma H Y W Z ≤ d H (A i) + d H (A j) := by sorry

end HyperKCut.Structure
