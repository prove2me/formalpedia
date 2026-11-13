-- Prove2me | Theorems.Thm_LowDiameterNashWilliams_Main_lemma_4_2_exists
-- name    : LowDiameterNashWilliams.Main.lemma_4_2_exists
-- status  : Proved
-- author  : @dbenbenn
-- created : 2026-11-12T21:31:54.660324+00:00
-- url     : https://prove2.me/theorems/f2cc577d-4ec6-41fb-bb33-ef76d66ffc84
-- title:
--   Lemma 4.2 (existence part) — outdegree-preserving shortening of a spanning tree
-- statement:
--   There is a constant $C_D > 0$ such that the following holds for all $n \ge 1$, $d \ge 1$ and every simple graph $G$ on the vertex set $\{0,\dots,n-1\}$ with edges $\{0,\dots,m-1\}$ (`Simple ends`: no loops, no two edges with the same ends). Let $T$ be a spanning tree of $G$, let $X$ be a set of vertices, and let $D$ orient every edge outside $T$ (`Orients ends (univ \ T) D`: each such edge $e$ runs from $D(e)_1$ to $D(e)_2$, its two ends) so that every vertex outside $X$ has outdegree at least $d$. Then there are a spanning tree $Q$ of $G$ and an orientation $D'$ of the edges outside $Q$ such that
--   $$\operatorname{diam}(Q) \le C_D\left(|X| + \frac{n}{d}\right)$$
--   (real division; `diameter` is the supremum of path distances in $Q$) and every vertex has the same outdegree in $D'$ on the edges outside $Q$ as in $D$ on the edges outside $T$.
--
--   This is the first, existential conjunct of the mission's `LowDiameterNashWilliams.Main.lemma_4_2`, without its second conjunct, the deterministic word-RAM program running in $O(dN^3)$ steps. The paper states Lemma 4.2 on p. 12: "Then there are a spanning tree $Q$ of $G$ and an orientation $D'$ of $E \setminus E(Q)$ such that $\operatorname{diam}(Q) = O(|X| + N/d)$, and every vertex has the same outdegree in $D'$ as in $D$." It proves the lemma in Section 5. The proof of Lemma 4.1 uses only this part.
-- source:
--   A Low-Diameter Nash-Williams–Tutte Theorem, STOC 2027 submission 1510 (https://github.com/sigact-stoc/stoc2027/releases/download/papers-2/1510.pdf), p. 12, 20-23, Lemma 4.2 (existence part), proved in Section 5.

import Mathlib
import Definitions.Def_LowDiameterNashWilliams_Main_Geometry

set_option autoImplicit false
open Classical
open scoped BigOperators ENNReal NNReal
open NashWilliams61.TreePacking NagamochiIbaraki.EdgeConn
open LowDiameterNashWilliams.Main

theorem LowDiameterNashWilliams.Main.lemma_4_2_exists :
  ∃ C_D : ℝ, 0 < C_D ∧
  ∀ n m d : ℕ, 1 ≤ n → 1 ≤ d →
  ∀ (ends : Fin m → Sym2 (Fin n)) (T : Edges m) (X : Finset (Fin n)) (D : Direction n m),
  Simple ends → IsSpanningTree ends T → Orients ends (Finset.univ \ T) D →
  (∀ v, v ∉ X → d ≤ outdegree (Finset.univ \ T) D v) →
  ∃ (Q : Edges m) (D' : Direction n m), IsSpanningTree ends Q ∧
    Orients ends (Finset.univ \ Q) D' ∧
    diameter ends Q ≤ ENNReal.ofReal (C_D * (X.card + (n : ℝ) / d)) ∧
    ∀ v, outdegree (Finset.univ \ Q) D' v = outdegree (Finset.univ \ T) D v := by sorry
