-- Prove2me | Theorems.Thm_L1ResistanceCount_Counting_lemma_4_2
-- name    : L1ResistanceCount.Counting.lemma_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:25.858833+00:00
-- url     : https://prove2.me/theorems/24c5041d-dbd5-4149-8fc7-5a636134322c
-- title:
--   Lemma 4.2 — exact aggregate resistance deficit
-- statement:
--   Let $G=(V,E,w)$ be connected, $n=|V|$, and $1/n<\lambda<1/2$. For each labelled edge $e$, write $R_e$ and $R_e^\lambda$ for its ordinary and regularized resistances. Then
--
--   $$\sum_{e\in E}w_e(R_e-R_e^\lambda)=\lambda n-1.$$
--
--   The equality retains the source's exact deficit, rather than replacing it with an asymptotic upper bound. Parallel edge labels contribute with their own weights.
--
--   Differences from the source:
--   - encoding: a finite weighted undirected graph on V with labelled edges E → the published positive-real-weight multigraph on Fin n and Fin m; reason: finite labels preserve every graph up to relabelling; parallel edges remain distinct and §2 discards loops
-- source:
--   Rong-Hua Li, Yichun Yang, STOC 2027 submission #881 (October 2026), Lemma 4.2, printed p.9 / PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/881.pdf

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Obstacle

namespace L1ResistanceCount.Counting

theorem lemma_4_2 {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (lam : ℝ) (hlam : 1 / (n : ℝ) < lam) (hlam' : lam < 1 / 2) :
    (∑ e, G.w e * (G.effRes e - regularizedResistance G lam (G.head e) (G.tail e))) =
      lam * (n : ℝ) - 1 := by sorry

end L1ResistanceCount.Counting
