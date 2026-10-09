-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_lemma_4_3
-- name    : LinearPathTuran.Exact.lemma_4_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:02.116221+00:00
-- url     : https://prove2.me/theorems/dc4b3803-082f-464d-9ac6-4c14fa96debd
-- title:
--   Lemma 4.3 — (k−1)|F| ≤ e(H′)·C(n−2, k−2) for the centre graph H′
-- statement:
--   Let $\mathcal F\subseteq\binom{[n]}{k}$ and choose for each $F\in\mathcal F$ a vertex $c(F)\in F$. Let $H'$ be the simple graph on $[n]$ whose edges are the pairs $\{c(F),y\}$ with $F\in\mathcal F$ and $y\in F\setminus\{c(F)\}$. Then
--   $$(k-1)\,|\mathcal F|\le e(H')\binom{n-2}{k-2},\qquad\text{i.e.}\quad |\mathcal F|\le\frac{e(H')}{k-1}\binom{n-2}{k-2}.$$
--
--   In the paper, $\mathcal F$ is partitioned into $(k,s)$-homogeneous pieces whose patterns have rank $k-1$ and type 1, $c(F)$ is the central element of $F$, and $H'$ is the underlying simple graph of the $(k,s)$-homogeneous kernel graph. The bound converts an edge bound on $H'$ into a bound on $|\mathcal F|$ (Theorem 4.5).
--
--   **Formalization Note** This is a disclosed generalization of the printed lemma: it is stated for an arbitrary choice $c(F)\in F$, which is all the paper's double-counting proof uses; the printed statement is the special case of the central elements. The quotient by $k-1$ is multiplied out.
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 8, Lemma 4.3 (with the definitions of the central element c(F) and of H′ on p. 8)

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

namespace LinearPathTuran.Exact

open Finset

open Classical in
/-- Lemma 4.3, p. 8, stated for an arbitrary choice of a vertex `c F ∈ F` of each member (the
page's `H'` is the case where `c F` is the central element of `F`). -/
theorem lemma_4_3 (k : ℕ) {n : ℕ} (𝓕 : Finset (Finset (Fin n)))
    (hU : 𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k)
    (c : Finset (Fin n) → Fin n) (hc : ∀ F ∈ 𝓕, c F ∈ F) :
    (k - 1) * #𝓕 ≤ #(centreGraph 𝓕 c).edgeFinset * (n - 2).choose (k - 2) := by sorry

end LinearPathTuran.Exact
