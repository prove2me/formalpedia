-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_theorem_2_4
-- name    : LinearPathTuran.Exact.theorem_2_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:37.952839+00:00
-- url     : https://prove2.me/theorems/a4a539ac-69db-44b4-aab4-48e143b59913
-- title:
--   Theorem 2.4 — for k ≥ 4 and large n, ex_k(n, ℙ_{2t+1}) = f(n,k,t) and ex_k(n, ℙ_{2t+2}) = g(n,k,t), with unique extremal families
-- statement:
--   **Main result.** Let $k,t$ be positive integers with $k\ge 4$. For every sufficiently large $n$:
--
--   1. $$\mathbf{ex}_k(n,\mathbb P^{(k)}_{2t+1})=\binom{n-1}{k-1}+\binom{n-2}{k-1}+\dots+\binom{n-t}{k-1},$$
--   and the only extremal family consists of all $k$-subsets of $[n]$ that meet some fixed set $S$ of $t$ elements;
--   2. $$\mathbf{ex}_k(n,\mathbb P^{(k)}_{2t+2})=\binom{n-1}{k-1}+\binom{n-2}{k-1}+\dots+\binom{n-t}{k-1}+\binom{n-t-2}{k-2},$$
--   and the only extremal family consists of all $k$-subsets of $[n]$ that meet some fixed set $S$ of $t$ elements together with all $k$-subsets of $[n]\setminus S$ that contain two fixed elements.
--
--   Here $\mathbb P^{(k)}_\ell$ is the $k$-uniform linear path of length $\ell$ ($\ell$ sets, consecutive ones sharing exactly one vertex, non-consecutive ones disjoint), and $\mathbf{ex}_k(n,\mathbb P^{(k)}_\ell)$ is the largest size of a $k$-uniform family on $[n]$ containing no copy of it. The theorem determines the Turán number of every $k$-uniform linear path exactly, for $k\ge 4$ and large $n$.
--
--   **Formalization Note** "Sufficiently large $n$" is $\exists n_0\,\forall n\ge n_0$, with $n_0$ depending only on $k$ and $t$. Each "only extremal family" clause is an equivalence: a family is $k$-uniform, $\mathbb P$-free and of the extremal size iff it is the named family for some $t$-set $S$ (and, in the even case, two distinct elements $u,v\notin S$); the backward direction records that the named families are extremal. The page writes the second Turán number as $\mathbf{ex}(n,\mathbb P^{(k)}_{2t+2})$, without the subscript $k$; it is the same $k$-uniform Turán number.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 3, Theorem 2.4

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_Setting

namespace LinearPathTuran.Exact

open Finset

/-- Theorem 2.4 (main result), p. 3. -/
theorem theorem_2_4 (k t : ℕ) (hk : 4 ≤ k) (ht : 1 ≤ t) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀,
      exLin n k (2 * t + 1) = fNum n k t ∧
      (∀ 𝓕 : Finset (Finset (Fin n)),
        (𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k ∧
            ¬ ContainsLinearPath 𝓕 (2 * t + 1) ∧ #𝓕 = fNum n k t) ↔
          ∃ S : Finset (Fin n), #S = t ∧ 𝓕 = starFamily n k S) ∧
      exLin n k (2 * t + 2) = gNum n k t ∧
      (∀ 𝓕 : Finset (Finset (Fin n)),
        (𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k ∧
            ¬ ContainsLinearPath 𝓕 (2 * t + 2) ∧ #𝓕 = gNum n k t) ↔
          ∃ (S : Finset (Fin n)) (u v : Fin n), #S = t ∧ u ∉ S ∧ v ∉ S ∧ u ≠ v ∧
            𝓕 = evenFamily n k S u v) := by sorry

end LinearPathTuran.Exact
