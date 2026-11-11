-- Prove2me | Theorems.Thm_L1ResistanceCount_Counting_lemma_3_8
-- name    : L1ResistanceCount.Counting.lemma_3_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-11T04:11:21.722772+00:00
-- url     : https://prove2.me/theorems/db3942dd-711e-4b65-8c7e-16497bda6365
-- title:
--   Lemma 3.8 — threshold rounding preserves a probability residual
-- statement:
--   Let $G$ be connected, $1/n<\lambda<1/2$, and fix a source $s$. Suppose $x\ge0$ and $|x_v-z_s^*(v)|\le\xi$ for every vertex, with $\xi\le\lambda/(12d_{\max})$. Define $\hat z_v=x_v$ when $x_v>2\xi$, and $\hat z_v=0$ otherwise. Then
--
--   $$\operatorname{supp}\hat z\subseteq\operatorname{supp}z_s^*,\qquad |\hat z_v-z_s^*(v)|\le3\xi,$$
--   $$0\le e_s-L\hat z\le\tfrac32\lambda\mathbf1,\qquad\sum_v(e_s-L\hat z)_v=1.$$
--
--   The coordinatewise approximation condition is equivalent to the source's infinity-norm inequality. It implies $\xi\ge0$ since the graph is nonempty, so no redundant sign hypothesis is added. This statement includes the exact-vector case $\xi=0$.
--
--   Differences from the source:
--   - encoding: a finite weighted undirected graph on V with labelled edges E → the published positive-real-weight multigraph on Fin n and Fin m; reason: finite labels preserve every graph up to relabelling; parallel edges remain distinct and §2 discards loops
--   - encoding: an infinity-norm bound → the equivalent pointwise absolute-error bounds over all finite coordinates; reason: this avoids an additional choice of normed vector representation without changing instances
-- source:
--   Rong-Hua Li, Yichun Yang, STOC 2027 submission #881 (October 2026), Lemma 3.8, printed p.8 / PDF p.8; https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/881.pdf

import Mathlib
import Definitions.Def_L1ResistanceCount_Counting_Obstacle

namespace L1ResistanceCount.Counting

theorem lemma_3_8 {n m : ℕ} (G : WeightedGraph n m) (hG : G.IsConnected)
    (lam : ℝ) (hlam : 1 / (n : ℝ) < lam) (hlam' : lam < 1 / 2) (s : Fin n)
    (x : Vector n) (ξ : ℝ) (hx : nonnegative x)
    (herror : ∀ v, |x v - obstaclePotential G lam s v| ≤ ξ)
    (hsmall : ξ ≤ lam / (12 * maximumDegree G)) :
    support (roundedPotential x ξ) ⊆ support (obstaclePotential G lam s) ∧
    (∀ v, |roundedPotential x ξ v - obstaclePotential G lam s v| ≤ 3 * ξ) ∧
    (∀ v, 0 ≤ residual G s (roundedPotential x ξ) v ∧
      residual G s (roundedPotential x ξ) v ≤ (3 / 2 : ℝ) * lam) ∧
    (∑ v, residual G s (roundedPotential x ξ) v) = 1 := by sorry

end L1ResistanceCount.Counting
