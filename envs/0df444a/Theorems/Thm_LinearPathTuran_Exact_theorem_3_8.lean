-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_theorem_3_8
-- name    : LinearPathTuran.Exact.theorem_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:25.038954+00:00
-- url     : https://prove2.me/theorems/3bdbad5d-1d72-4898-8565-77a6abb51964
-- title:
--   Theorem 3.8 — a homogeneous family of rank k or type 2 contains the k-blowup of every q-edge tree when s ≥ kq
-- statement:
--   Let $k\ge 4$, $q\ge 1$ and $s\ge kq$. Let $T$ be a tree with $q$ edges, and let $\mathcal F^*$ be a nonempty $(k,s)$-homogeneous family with intersection pattern $\mathcal J$. If $\mathcal J$ has rank $k$, or has rank $k-1$ and is of type 2, then
--   $$T^{(k)}\subseteq\mathcal F^*,$$
--   i.e. $\mathcal F^*$ contains a copy of the $k$-blowup of $T$.
--
--   Since a linear path $\mathbb P_\ell^{(k)}$ is the $k$-blowup of the path with $\ell$ edges, a $\mathbb P_\ell^{(k)}$-free family has no large homogeneous piece of this kind; this is what forces the canonical partition of Theorem 3.9.
--
--   **Formalization Note** The tree is a graph on $q+1$ vertices; a copy of $T^{(k)}$ is an embedding of the vertices of $T$ into $[n]$ together with members of $\mathcal F^*$ realising the blowup. The hypothesis that $\mathcal F^*$ is nonempty is added: the empty family is $(k,s)$-homogeneous for every proper intersection-closed $\mathcal J$, and the paper's proof starts from "any member $F\in\mathcal F^*$".
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 6, Theorem 3.8

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

namespace LinearPathTuran.Exact

open Finset

/-- Theorem 3.8, p. 6: a nonempty `(k, s)`-homogeneous family whose pattern has rank `k`, or rank
`k - 1` and type 2, contains the `k`-blowup of every tree with `q` edges when `s ≥ kq`. -/
theorem theorem_3_8 (k s q : ℕ) (hk : 4 ≤ k) (hq : 1 ≤ q) (hs : k * q ≤ s)
    (T : SimpleGraph (Fin (q + 1))) (hT : T.IsTree) {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (χ : Fin n → Fin k) (J : Finset (Finset (Fin k)))
    (hH : IsHomogeneous s 𝓕 χ J) (hne : 𝓕.Nonempty)
    (hJ : rank J = k ∨ (rank J = k - 1 ∧ ¬ IsType1 J)) :
    ContainsBlowup 𝓕 T := by sorry

end LinearPathTuran.Exact
