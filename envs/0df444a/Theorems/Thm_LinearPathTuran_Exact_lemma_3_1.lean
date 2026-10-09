-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_lemma_3_1
-- name    : LinearPathTuran.Exact.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:10.72899+00:00
-- url     : https://prove2.me/theorems/755594d1-c51c-4692-8280-c4a3d5a87fe7
-- title:
--   Lemma 3.1 — the intersection semilattice lemma: every k-uniform family has a (k,s)-homogeneous subfamily of proportional size
-- statement:
--   **Intersection semilattice lemma (Füredi 1983).** For all positive integers $k$ and $s$ there is a constant $c(k,s)>0$ such that every family $\mathcal F\subseteq\binom{[n]}{k}$, for every $n$, contains a subfamily $\mathcal F^*\subseteq\mathcal F$ with
--   $$|\mathcal F^*|\ge c(k,s)\,|\mathcal F|$$
--   which is $(k,s)$-homogeneous: it is $k$-partite with some $k$-partition $(X_1,\dots,X_k)$; there is a family $\mathcal J$ of proper subsets of $[k]$ with $\Pi(\mathcal I(F,\mathcal F^*))=\mathcal J$ for all $F\in\mathcal F^*$; $\mathcal J$ is closed under intersection; and for every $F\in\mathcal F^*$ and $A\in\mathcal I(F,\mathcal F^*)$ there is an $s$-star in $\mathcal F^*$ containing $F$ with kernel $A$.
--
--   This is the structural engine of the delta-system method: it reduces any $k$-uniform family, at the cost of a constant factor, to one whose intersections are governed by a single semilattice $\mathcal J$ on $[k]$.
--
--   **Formalization Note** The constant $c$ is chosen after $k,s$ and before $n$ and $\mathcal F$, so it depends only on $k$ and $s$. The $k$-partition is a part map `χ : Fin n → Fin k`. The lemma is cited in the paper from Füredi (1983) and not proved there.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, pp. 4–5, Lemma 3.1 (cited from Füredi, On finite set-systems whose every intersection is a kernel of a star, Discrete Math. 47 (1983))

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

namespace LinearPathTuran.Exact

open Finset

/-- Lemma 3.1 (the intersection semilattice lemma, Füredi 1983), pp. 4–5. -/
theorem lemma_3_1 (k s : ℕ) (hk : 1 ≤ k) (hs : 1 ≤ s) :
    ∃ c : ℝ, 0 < c ∧ ∀ (n : ℕ) (𝓕 : Finset (Finset (Fin n))),
      𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k →
      ∃ 𝓕' ⊆ 𝓕, ∃ (χ : Fin n → Fin k) (J : Finset (Finset (Fin k))),
        c * (#𝓕 : ℝ) ≤ #𝓕' ∧ IsHomogeneous s 𝓕' χ J := by sorry

end LinearPathTuran.Exact
