-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_corollary_3_7
-- name    : LinearPathTuran.Exact.corollary_3_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:02.486183+00:00
-- url     : https://prove2.me/theorems/8ef2b0e6-e274-46b2-aa8b-96bcfac25f3c
-- title:
--   Corollary 3.7 — rank k or type 2: every member has two vertices that are kernels of s-stars
-- statement:
--   Let $s\ge k\ge 4$ and let $\mathcal F^*$ be a $(k,s)$-homogeneous family with intersection pattern $\mathcal J$, where $\mathcal J$ has rank $k$, or has rank $k-1$ and is of type 2. Then every $F\in\mathcal F^*$ contains two distinct vertices $u,v$ such that
--   $$\deg^*_{\mathcal F^*}(\{u\})\ge s\quad\text{and}\quad \deg^*_{\mathcal F^*}(\{v\})\ge s,$$
--   i.e. $\{u\}$ and $\{v\}$ are each the kernel of some $s$-star in $\mathcal F^*$.
--
--   It supplies the "kernel vertices" from which Theorem 3.8 grows blowups of trees.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 6, Corollary 3.7

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

namespace LinearPathTuran.Exact

open Finset

/-- Corollary 3.7, p. 6. -/
theorem corollary_3_7 (k s : ℕ) (hk : 4 ≤ k) (hs : k ≤ s) {n : ℕ}
    (𝓕 : Finset (Finset (Fin n))) (χ : Fin n → Fin k) (J : Finset (Finset (Fin k)))
    (hH : IsHomogeneous s 𝓕 χ J) (hJ : rank J = k ∨ (rank J = k - 1 ∧ ¬ IsType1 J))
    (F : Finset (Fin n)) (hF : F ∈ 𝓕) :
    ∃ u ∈ F, ∃ v ∈ F, u ≠ v ∧ HasStar 𝓕 {u} s ∧ HasStar 𝓕 {v} s := by sorry

end LinearPathTuran.Exact
