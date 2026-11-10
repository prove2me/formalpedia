-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_1_7
-- name    : MaxIsoVertexCuts.Shredders.lemma_1_7
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:00:58.105329+00:00
-- url     : https://prove2.me/theorems/9d4f93fc-8c31-440b-a2d2-f4a17530f55b
-- title:
--   Lemma 1.7 — A vertex in exactly one shore is in at most one separator; a vertex in two or more shores is in no separator
-- statement:
--   Let T be independent in a graph with strictly positive real vertex weights, and let A_i⊆T be r≥2 pairwise disjoint nonempty subsets. For arbitrary minimum (A_i,T−A_i)-shores L_i, with S_i=N(L_i), every vertex in exactly one L_i lies in at most one S_i, and every vertex in at least two L_i lies in no S_i. No maximality or reachability of these shores is assumed.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - generalization: positive polynomially bounded vertex weights → arbitrary strictly positive real vertex weights; reason: no weight bound is needed in these structural claims; every source instance remains covered
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 1.7, printed p.6 (PDF p.8)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_1_7 {n r : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (hw : Positive w) (T : VSet n) (A L : Fin r → VSet n)
    (hT : Independent G T) (hr : 2 ≤ r)
    (hA : ∀ i, (A i).Nonempty ∧ A i ⊆ T) (hdis : Pairwise (fun i j => Disjoint (A i) (A j)))
    (hL : ∀ i, IsMinShore G w (A i) (T \ A i) (L i)) :
    (∀ v, (Finset.univ.filter fun i => v ∈ L i).card = 1 →
      (Finset.univ.filter fun i => v ∈ HypRecov.nbhd G (L i)).card ≤ 1) ∧
    (∀ v, 2 ≤ (Finset.univ.filter fun i => v ∈ L i).card →
      ∀ i, v ∉ HypRecov.nbhd G (L i)) := by sorry

end MaxIsoVertexCuts.Shredders
