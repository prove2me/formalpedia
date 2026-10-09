-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_lemma_3_6
-- name    : LinearPathTuran.Exact.lemma_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:23:36.994597+00:00
-- url     : https://prove2.me/theorems/ce6e5dec-a3ac-4633-9b48-4460a24e7c96
-- title:
--   Lemma 3.6 — intersection-closed families of proper subsets of [k] of rank k and k−1
-- statement:
--   Let $k\ge 3$ and let $\mathcal L$ be a family of proper subsets of $[k]$ that is closed under intersection.
--
--   1. If $r(\mathcal L)=k$, then $\mathcal L$ consists of all proper subsets of $[k]$.
--   2. If $r(\mathcal L)=k-1$ and $\mathcal L$ is of type 1, then for some $i\in[k]$ (the *central element*), $\mathcal L$ contains every proper subset of $[k]$ that contains $i$.
--   3. If $k\ge 4$, $r(\mathcal L)=k-1$ and $\mathcal L$ is of type 2, then $\mathcal L$ contains at least two singletons:
--   $$\exists\, i\neq j\in[k]:\quad \{i\}\in\mathcal L,\ \{j\}\in\mathcal L .$$
--
--   The lemma classifies the intersection patterns of large homogeneous families: type 2 and rank $k$ yield two singleton kernels (hence long paths), and type 1 yields a central vertex in every member.
--
--   **Formalization Note** "Type 2" is written as rank $k-1$ and not of type 1, exactly as Definition 3.5 defines it.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 6, Lemma 3.6

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

namespace LinearPathTuran.Exact

open Finset

/-- Lemma 3.6, p. 6: intersection-closed families of proper subsets of `[k]` of rank `k` and `k - 1`. -/
theorem lemma_3_6 (k : ℕ) (hk : 3 ≤ k) (L : Finset (Finset (Fin k)))
    (hproper : ∀ A ∈ L, A ≠ univ) (hcap : ∀ A ∈ L, ∀ B ∈ L, A ∩ B ∈ L) :
    (rank L = k → ∀ A : Finset (Fin k), A ≠ univ → A ∈ L) ∧
    (rank L = k - 1 → IsType1 L →
        ∃ i : Fin k, ∀ A : Finset (Fin k), A ≠ univ → i ∈ A → A ∈ L) ∧
    (4 ≤ k → rank L = k - 1 → ¬ IsType1 L →
        ∃ i j : Fin k, i ≠ j ∧ {i} ∈ L ∧ {j} ∈ L) := by sorry

end LinearPathTuran.Exact
