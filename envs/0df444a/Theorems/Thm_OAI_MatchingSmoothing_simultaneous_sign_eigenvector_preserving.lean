-- Prove2me | Theorems.Thm_OAI_MatchingSmoothing_simultaneous_sign_eigenvector_preserving
-- name    : OAI.MatchingSmoothing.simultaneous_sign_eigenvector_preserving
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T04:27:08.397267+00:00
-- url     : https://prove2.me/theorems/67a5b0b4-e88d-4e25-adf6-1217d164646a
-- title:
--   Common $\pm1$ eigenvector of commuting involutions extending prescribed eigenvalues
-- statement:
--   Let $\iota$ be a finite index set and $V$ a real vector space (not necessarily finite-dimensional). Let $(A_i)_{i\in\iota}$ be linear maps $V\to V$ that commute pairwise, $A_iA_j=A_jA_i$ for all $i,j$, and are involutions, $A_i(A_iu)=u$ for all $i$ and all $u\in V$. Let $W\subseteq V$ be a linear subspace with $A_iW\subseteq W$ for every $i\in\iota$. Let $s\subseteq\iota$, let $\chi:\iota\to\mathbb{R}$, and let $v\in W$ with $v\neq0$ satisfy $A_iv=\chi_i\,v$ for all $i\in s$. Then there exist $\psi:\iota\to\mathbb{R}$ and $w\in W$ with $w\neq0$ such that
--   $$
--   \psi_i\in\{1,-1\}\ \text{ and }\ A_iw=\psi_i\,w\quad\text{for all } i\in\iota,\qquad\text{and}\qquad \psi_i=\chi_i\quad\text{for all } i\in s.
--   $$
--
--   In words: if an invariant subspace contains a nonzero joint eigenvector for the involutions indexed by $s$, then it also contains a nonzero joint eigenvector for all the involutions, with the same eigenvalues on $s$. In particular the prescribed values $\chi_i$, $i\in s$, are necessarily $\pm1$. In the matching argument the involutions are the swaps of the two vertices of the standard pairs, acting on functions of matchings, and the lemma produces inside a permutation-invariant space of functions a joint eigenvector whose sign pattern is prescribed on part of the pairs.
--
--   **Formalization Note** The maps are elements of `Module.End ℝ V`, commutation is `Commute (A i) (A j)` for all `i j`, finiteness of the index set is a `Fintype ι` instance, and $s$ is a `Finset ι`. No hypothesis restricts $\chi$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/Involutions.lean#L79-L107

import Mathlib
import Definitions.Def_MatchingPSD

open OAI
universe u_1 u_2 u_3
variable {ι : Type u_1} {V : Type u_2} [AddCommGroup V] [Module ℝ V]

theorem OAI.MatchingSmoothing.simultaneous_sign_eigenvector_preserving [Fintype ι]
    (A : ι → Module.End ℝ V) (hcomm : ∀ i j, Commute (A i) (A j))
    (hinv : ∀ i v, A i (A i v) = v)
    (W : Submodule ℝ V) (hstable : ∀ i v, v ∈ W → A i v ∈ W)
    (s : Finset ι) (χ : ι → ℝ)
    (v : V) (hv : v ∈ W) (hv0 : v ≠ 0) (he : ∀ i ∈ s, A i v = χ i • v) :
    ∃ (ψ : ι → ℝ) (w : V), w ∈ W ∧ w ≠ 0 ∧
      (∀ i, (ψ i = 1 ∨ ψ i = -1) ∧ A i w = ψ i • w) ∧
      ∀ i ∈ s, ψ i = χ i := by sorry
