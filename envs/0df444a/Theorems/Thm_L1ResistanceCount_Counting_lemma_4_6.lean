-- Prove2me | Theorems.Thm_L1ResistanceCount_Counting_lemma_4_6
-- name    : L1ResistanceCount.Counting.lemma_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:22.622993+00:00
-- url     : https://prove2.me/theorems/bc0cb301-5130-47f2-b656-8b1565e10b5d
-- title:
--   Lemma 4.6 — graph maximum principle
-- statement:
--   Let $G$ be a finite connected positive-weight undirected graph with Laplacian $L$, and let $p$ be any real vertex vector. Assume $p$ has at least one nonpositive coordinate, and $(Lp)_v\le0$ at every vertex where $p_v>0$. Then
--
--   $$p_v\le0\quad\text{for every vertex }v.$$
--
--   No stronger boundary condition, normalization, or strict inequality is imposed. The result supplies the maximum principle used to control row potentials in the paper.
--
--   Differences from the source:
--   - encoding: a finite weighted undirected graph on V with labelled edges E → the published positive-real-weight multigraph on Fin n and Fin m; reason: finite labels preserve every graph up to relabelling; parallel edges remain distinct and §2 discards loops
-- source:
--   Rong-Hua Li, Yichun Yang, STOC 2027 submission #881 (October 2026), Lemma 4.6, printed p.14 / PDF p.14; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/881.pdf

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Obstacle

namespace L1ResistanceCount.Counting

theorem lemma_4_6 {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (p : Vector n) (hboundary : ∃ v, p v ≤ 0)
    (hsubharmonic : ∀ v, 0 < p v → G.laplacian.mulVec p v ≤ 0) :
    ∀ v, p v ≤ 0 := by sorry

end L1ResistanceCount.Counting
