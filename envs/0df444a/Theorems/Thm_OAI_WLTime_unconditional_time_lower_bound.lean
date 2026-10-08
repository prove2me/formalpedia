-- Prove2me | Theorems.Thm_OAI_WLTime_unconditional_time_lower_bound
-- name    : OAI.WLTime.unconditional_time_lower_bound
-- status  : Open
-- author  : @wurtle
-- created : 2026-10-07T04:33:38.249603+00:00
-- url     : https://prove2.me/theorems/480c4346-cb15-48cb-8208-b62e388748ee
-- statement:
--   The theorem states that there are a real constant c>0 and a threshold k₀ such that, for every k ≥ k₀, every convention (joint or separate), every input class (all pairs of graphs, or only pairs in which both graphs have diameter two) and every computational model that decides k-dimensional Weisfeiler-Leman equivalence on that class, the worst-case running time grows at least like n^(ck). Here a graph on n vertices is a symmetric loopless Boolean adjacency matrix, and diameter two means n>0 and any two distinct vertices are equal, adjacent or share a common neighbour. A k-tuple of vertices has an atomic color recording its equality pattern and adjacency pattern, and the round-t color refines the previous color by the multiset, over replacement of one coordinate i by every vertex z, of the refined colors (the joint convention records a multiset of k-coordinate functions, the separate convention records one multiset per coordinate). Two graphs on n vertices are k-WL equivalent when their histograms of tuple colors agree at every round t. A model is either a multi-tape Turing machine or a word RAM with logarithmic word width, registers, a program and word operations implemented by polynomial-time Turing machines; its input is a binary encoding of n followed by both adjacency matrices. The model decides the class if, for all n and all admissible pairs, it halts and accepts exactly when the graphs are k-WL equivalent. Worst time is the maximum halting time over admissible pairs on n vertices, and the conclusion holds for all n ≥ some n₀ depending on the model, k, convention and class.
-- source:
--   https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/lean/ComparatorChallenges/WeisfeilerLeman.lean

-- Generated from openai/math @ adc7f1241b42e322a6451854ab7e4b4c146bf78a
-- Source: lean/ComparatorChallenges/WeisfeilerLeman.lean; bytes 9062..9140
-- Kind: theorem; original declaration names and bodies preserved.
-- Source groups are independent. Target: Lean 4.33.1; see compilation.json.

import Mathlib
import Definitions.Def_WeisfeilerLeman

namespace OAI

theorem WLTime.unconditional_time_lower_bound : WLTime.MainClaim := by
  sorry

end OAI
