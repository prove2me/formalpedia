-- Prove2me | Theorems.Thm_LinearPathTuran_Exact_lemma_4_2
-- name    : LinearPathTuran.Exact.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T19:22:10.809545+00:00
-- url     : https://prove2.me/theorems/238db6cf-25ac-4043-afe7-1fbcee2889d7
-- title:
--   Lemma 4.2 — a q-edge graph inside the kernel graph with threshold kq yields a copy of its k-blowup
-- statement:
--   Let $k\ge2$, let $H$ be a graph on $[n]$ with $q$ edges, let $s=kq$, and let $\mathcal F\subseteq\binom{[n]}{k}$. Let $L$ be the kernel graph of $\mathcal F$ with threshold $s$. If $H\subseteq L$, then $\mathcal F$ contains a copy of $H^{(k)}$ whose skeleton is $H$: each edge $xy$ of $H$ is realised by a member $E_{xy}\in\mathcal F$ containing $x$ and $y$ whose remaining $k-2$ vertices avoid the vertices of $H$, and
--   $$(E_{xy}\setminus\{x,y\})\cap(E_{x'y'}\setminus\{x',y'\})=\emptyset\quad\text{for distinct edges } xy,\ x'y'.$$
--
--   This turns path-like structures in the kernel graph into linear paths of $\mathcal F$.
--
--   **Formalization Note** $H\subseteq L$ is the subgraph relation `H ≤ kernelGraph 𝓕 (k * q)`. The page's blowup uses $k-2$ new vertices and thus presupposes $k\ge2$; this is explicit in Lean because at $k=0$ the zero threshold would make every pair a kernel-graph edge. The requirement that the new vertices avoid every vertex of $H$ is the paper's "k − 2 new vertices" (p. 6).
-- source:
--   Füredi, Jiang and Seiver, Exact solution of the hypergraph Turán problem for k-uniform linear paths, arXiv:1108.1247v1, p. 7, Lemma 4.2

import Mathlib
import Definitions.Def_LinearPathTuran_Exact_DeltaSystem

namespace LinearPathTuran.Exact

open Finset

/-- Lemma 4.2, p. 7: a graph `H` with `q` edges inside the kernel graph with threshold `kq`
yields a copy of `H^(k)` with skeleton `H`. -/
theorem lemma_4_2 (k q : ℕ) (hk : 2 ≤ k) {n : ℕ} (H : SimpleGraph (Fin n)) [DecidableRel H.Adj]
    (hq : #H.edgeFinset = q) (𝓕 : Finset (Finset (Fin n)))
    (hU : 𝓕 ⊆ (univ : Finset (Fin n)).powersetCard k) (hHL : H ≤ kernelGraph 𝓕 (k * q)) :
    ContainsBlowupOn 𝓕 H := by sorry

end LinearPathTuran.Exact
