-- Prove2me | Theorems.Thm_LinearCrossingInequality
-- name    : LinearCrossingInequality
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-26T20:44:38.919395+00:00
-- url     : https://prove2.me/theorems/f81d8d9e-13cc-44dd-8aaf-0f22c5a75bc4
-- title:
--   Linear crossing-number inequality
-- statement:
--   For a finite simple graph $G$ on vertex set $V$, the minimum crossing number is bounded below by the excess of edges over the planar threshold:
--
--   $$
--   |E(G)|-3|V|\le \operatorname{CrossingNumber}(G).
--   $$
--
--   Here the crossing number is the minimum cardinality of the finite crossing set among ordinary polygonal drawings of $G$. This is the linear inequality used in the probabilistic proof of the crossing lemma: every induced subgraph contributes its edge surplus beyond $3|V|$ to the crossing count.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/LinearCrossingInequality.lean#L1-L71

import Definitions.Def_CrossingNumber

open Classical
noncomputable section

lemma LinearCrossingInequality {V : Type*} [Fintype V] (G : SimpleGraph V)
    [Fintype G.edgeSet] :
    (G.edgeFinset.card : ℤ) - 3 * (Fintype.card V : ℤ) ≤
      (CrossingNumber G : ℤ) := by sorry
