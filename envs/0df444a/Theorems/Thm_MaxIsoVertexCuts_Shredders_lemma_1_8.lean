-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_1_8
-- name    : MaxIsoVertexCuts.Shredders.lemma_1_8
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:01:11.570979+00:00
-- url     : https://prove2.me/theorems/da1b7ebe-e0fe-4b73-b126-770b7982885b
-- title:
--   Lemma 1.8 — Triple intersection: N(X∩Y∩Z) ⊆ N(X)∩N(Y)∩N(Z), and X∩Y∩Z = ∅ when G[X] is A-reachable
-- statement:
--   Let T be independent in a graph with strictly positive real vertex weights, and let A,B,C be nonempty pairwise disjoint proper subsets of T. For arbitrary minimum shores X,Y,Z of their respective terminal bipartitions, N(X∩Y∩Z)⊆N(X)∩N(Y)∩N(Z). Furthermore, if G[X] is A-reachable, X∩Y∩Z is empty.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - generalization: positive polynomially bounded vertex weights → arbitrary strictly positive real vertex weights; reason: no weight bound is needed in these structural claims; every source instance remains covered
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 1.8, printed p.7 (PDF p.9)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_1_8 {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (hw : Positive w) (T A B C X Y Z : VSet n) (hT : Independent G T)
    (hA : A.Nonempty) (hB : B.Nonempty) (hC : C.Nonempty)
    (hAT : A ⊂ T) (hBT : B ⊂ T) (hCT : C ⊂ T)
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hBC : Disjoint B C)
    (hX : IsMinShore G w A (T \ A) X) (hY : IsMinShore G w B (T \ B) Y)
    (hZ : IsMinShore G w C (T \ C) Z) :
    HypRecov.nbhd G (X ∩ Y ∩ Z) ⊆ HypRecov.nbhd G X ∩ HypRecov.nbhd G Y ∩ HypRecov.nbhd G Z ∧
    (AReachable G X A → X ∩ Y ∩ Z = ∅) := by sorry

end MaxIsoVertexCuts.Shredders
