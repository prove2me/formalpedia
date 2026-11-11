-- Prove2me | Theorems.Thm_L1ResistanceCount_Counting_lemma_4_1
-- name    : L1ResistanceCount.Counting.lemma_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:07.304499+00:00
-- url     : https://prove2.me/theorems/939c02d5-00aa-43c6-8558-7c18876d2463
-- title:
--   Lemma 4.1 — pointwise regularized-resistance bounds
-- statement:
--   Let $G$ be connected with positive real edge weights, and let $1/n<\lambda<1/2$. For distinct vertices $s,t$, let $R_{s,t}$ be the effective resistance and $R^\lambda_{s,t}$ the regularized resistance defined from the unique obstacle potentials. Then
--
--   $$0\le R^\lambda_{s,t}\le R_{s,t}.$$
--
--   This compares the independently defined regularized and ordinary resistances; neither inequality is assumed in their definitions.
--
--   Differences from the source:
--   - encoding: a finite weighted undirected graph on V with labelled edges E → the published positive-real-weight multigraph on Fin n and Fin m; reason: finite labels preserve every graph up to relabelling; parallel edges remain distinct and §2 discards loops
-- source:
--   Rong-Hua Li, Yichun Yang, STOC 2027 submission #881 (October 2026), Lemma 4.1, printed p.9 / PDF p.9; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/881.pdf

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Obstacle

namespace L1ResistanceCount.Counting

theorem lemma_4_1 {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (lam : ℝ) (hlam : 1 / (n : ℝ) < lam) (hlam' : lam < 1 / 2)
    (s t : Fin n) (hst : s ≠ t) :
    0 ≤ regularizedResistance G lam s t ∧
    regularizedResistance G lam s t ≤ pairResistance G s t := by sorry

end L1ResistanceCount.Counting
