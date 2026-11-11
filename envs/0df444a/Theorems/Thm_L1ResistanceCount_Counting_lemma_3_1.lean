-- Prove2me | Theorems.Thm_L1ResistanceCount_Counting_lemma_3_1
-- name    : L1ResistanceCount.Counting.lemma_3_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:05.355196+00:00
-- url     : https://prove2.me/theorems/6bc21a3a-8e30-40d6-843a-df5261d6372b
-- title:
--   Lemma 3.1 — existence, uniqueness, and obstacle structure
-- statement:
--   Let $G$ be connected, let $n$ be its vertex count, let $1/n<\lambda<1/2$, and fix a source $s$. The nonnegative obstacle objective has exactly one minimizer $z_s^*$. For $q_s^*=e_s-Lz_s^*$,
--
--   $$0\le q_s^*\le\lambda\mathbf1,\qquad\sum_v q_s^*(v)=1,$$
--   $$z_s^*(v)>0\Longrightarrow q_s^*(v)=\lambda,\qquad |\operatorname{supp}z_s^*|\le\lambda^{-1}.$$
--
--   Moreover, $s\in\operatorname{supp}z_s^*$ and $q_s^*(s)=\lambda$. The theorem also identifies the chosen mathematical potential with that minimizer. These are conclusions, rather than assumptions used to define the optimizer.
--
--   Differences from the source:
--   - encoding: a finite weighted undirected graph on V with labelled edges E → the published positive-real-weight multigraph on Fin n and Fin m; reason: finite labels preserve every graph up to relabelling; parallel edges remain distinct and §2 discards loops
--   - encoding: the optimizer is denoted by an argmin → existence and uniqueness are asserted separately and the chosen potential is asserted to be a minimizer; reason: the potential has a total zero default outside the unique-minimizer domain; no optimizer existence is assumed
-- source:
--   Rong-Hua Li, Yichun Yang, STOC 2027 submission #881 (October 2026), Lemma 3.1, printed p.4 / PDF p.4; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/881.pdf

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Obstacle

namespace L1ResistanceCount.Counting

theorem lemma_3_1 {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (lam : ℝ) (hlam : 1 / (n : ℝ) < lam) (hlam' : lam < 1 / 2) (s : Fin n) :
    (∃! z, IsObstacleMinimizer G lam s z) ∧
    IsObstacleMinimizer G lam s (obstaclePotential G lam s) ∧
    (∀ v, 0 ≤ exactResidual G lam s v ∧ exactResidual G lam s v ≤ lam) ∧
    (∑ v, exactResidual G lam s v) = 1 ∧
    (∀ v, 0 < obstaclePotential G lam s v → exactResidual G lam s v = lam) ∧
    ((support (obstaclePotential G lam s)).card : ℝ) ≤ 1 / lam ∧
    s ∈ support (obstaclePotential G lam s) ∧ exactResidual G lam s s = lam := by sorry

end L1ResistanceCount.Counting
