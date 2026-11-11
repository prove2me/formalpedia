-- Prove2me | Theorems.Thm_L1ResistanceCount_Counting_lemma_2_2
-- name    : L1ResistanceCount.Counting.lemma_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:17.015205+00:00
-- url     : https://prove2.me/theorems/4e0a49e5-233f-4d24-86b3-4a472e2651b3
-- title:
--   Lemma 2.2 — weighted matrix–tree theorem
-- statement:
--   Let $G$ be a finite connected positive-real-weight undirected graph, let $L$ be its Laplacian, and let $r$ be any root. With $T(G)$ defined as the weighted sum over spanning edge sets,
--
--   $$T(G)=\det L[V\setminus\{r\},V\setminus\{r\}].$$
--
--   The sum is independent of the cofactor in its definition. For a singleton, the cofactor is the empty determinant and the unique empty tree has weight one. The identity links combinatorial tree weights to the determinant identities used later in the paper.
--
--   Differences from the source:
--   - encoding: a finite weighted undirected graph on V with labelled edges E → the published positive-real-weight multigraph on Fin n and Fin m; reason: finite labels preserve every graph up to relabelling; parallel edges remain distinct and §2 discards loops
-- source:
--   Rong-Hua Li, Yichun Yang, STOC 2027 submission #881 (October 2026), Lemma 2.2, printed p.4 / PDF p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/881.pdf

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Obstacle

namespace L1ResistanceCount.Counting

theorem lemma_2_2 {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected) (r : Fin n) :
    treeWeight G = Matrix.det (G.laplacian.submatrix
      (fun v : {v : Fin n // v ≠ r} => v.val) (fun v : {v : Fin n // v ≠ r} => v.val)) := by sorry

end L1ResistanceCount.Counting
