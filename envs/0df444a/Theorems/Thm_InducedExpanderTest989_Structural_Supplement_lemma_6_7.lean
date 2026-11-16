-- Prove2me | Theorems.Thm_InducedExpanderTest989_Structural_Supplement_lemma_6_7
-- name    : InducedExpanderTest989.Structural.Supplement.lemma_6_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-15T20:32:12.006492+00:00
-- url     : https://prove2.me/theorems/6eb2b8a1-9979-4520-a74b-01c9e3c654f7
-- title:
--   Lemma 6.7 — averaging over small classes bounds inner conductance
-- statement:
--   Let $G$ be a simple graph on $[n]$ of maximum degree at most $d>0$, with inner conductance $\Phi_{\rm in}$ normalized by $d$. Suppose its vertex set is partitioned into classes of size at most $s\ge1$, and let $F$ be the set of edges joining different classes. Then every $U\subseteq V(G)$ of size $u>s$ satisfies
--   $$\Phi_{\rm in}(G[U])\le\frac{2|F|}{d\,\min\{u,\,2(u-s)\}},$$
--   and in particular, if $u\ge2s$, then $\Phi_{\rm in}(G[U])\le 2|F|/(du)$.
--
--   A large set must meet several small classes, and the edges between classes then bound its inner conductance. In the lower bound of Theorem 6.1 this gives the NO property of the planted instances.
--
--   **Formalization Note** The partition is a labelling $C:[n]\to\{0,\dots,m-1\}$ with classes `part C i`; $|F|$ is the mission's `crossEdges G C`, which counts each edge joining different classes once.
--
--   Differences from the source:
--   - encoding: a partition into classes of size at most s → a labelling C : Fin n → Fin m with every class of card ≤ s (empty classes allowed); reason: every partition has such a labelling and empty classes change nothing
-- source:
--   Pan Peng, Ranran Shen, Testing for a Large Induced Expander: Sublinear Algorithms and Query Lower Bounds, STOC 2027 submission #989 (October 2026), source.pdf SHA-256 98b4035a0ac121d1c1bfb6abdeb3cdb6cf3304ef3cb21b2cd58c97e4bbce6334, p.40 (PDF p.42), Lemma 6.7

import Mathlib
import Definitions.Def_InducedExpanderTest989_Structural_Graph

set_option autoImplicit false
open scoped BigOperators ENNReal NNReal
noncomputable section

namespace InducedExpanderTest989.Structural.Supplement

/-- Peng–Shen, STOC 2027 #989, Lemma 6.7 (p. 40, PDF 42). The partition of `V(G) = [n]` is the
labelling `C` (classes `part C i`); `|F| = crossEdges G C` counts each edge joining different
classes once. -/
theorem lemma_6_7 {n m : ℕ} (d : ℕ) (hd : 0 < d) (G : SimpleGraph (Fin n)) (hG : DegreeBound d G)
    (s : ℕ) (hs : 1 ≤ s) (C : Fin n → Fin m) (hC : ∀ i, (part C i).card ≤ s)
    (U : Finset (Fin n)) (hU : s < U.card) :
    innerConductance d G U ≤
        2 * (crossEdges G C : ℝ) /
          (d * min (U.card : ℝ) (2 * ((U.card : ℝ) - s))) ∧
      (2 * s ≤ U.card → innerConductance d G U ≤ 2 * (crossEdges G C : ℝ) / (d * U.card)) := by sorry

end InducedExpanderTest989.Structural.Supplement
