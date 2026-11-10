-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_4_2
-- name    : MaxIsoVertexCuts.Shredders.lemma_4_2
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:01:21.603881+00:00
-- url     : https://prove2.me/theorems/78cdcc60-1fa6-46e8-8736-81775f539fc6
-- title:
--   Lemma 4.2 — Uniqueness of the maximal minimum (A, T\A)-cut (Definition 4.1)
-- statement:
--   For a finite graph with strictly positive real vertex weights, an independent terminal set T and ∅⊂A⊂T, there exists exactly one maximal minimum (A,T−A)-cut, with maximality taken among cuts whose induced A-shore is A-reachable.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - generalization: positive polynomially bounded vertex weights → arbitrary strictly positive real vertex weights; reason: no weight bound is needed in these structural claims; every source instance remains covered
--   - reading: the maximal minimum cut is unique → there exists exactly one maximal A-reachable minimum cut; reason: the definite description and its subsequent algorithmic use include existence
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 4.2, printed p.23 (PDF p.25)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_4_2 {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (hw : Positive w) (T A : VSet n) (hT : Independent G T)
    (hA : A.Nonempty) (hAT : A ⊂ T) : ∃! c, IsMaxMinCut G w T A c := by sorry

end MaxIsoVertexCuts.Shredders
