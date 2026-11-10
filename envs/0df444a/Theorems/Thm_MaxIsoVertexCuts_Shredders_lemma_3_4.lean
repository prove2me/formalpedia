-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_3_4
-- name    : MaxIsoVertexCuts.Shredders.lemma_3_4
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-10T00:01:06.864921+00:00
-- url     : https://prove2.me/theorems/149a0cf9-3e51-4515-aebc-9e738b7513fd
-- title:
--   Lemma 3.4 — Intersection and union of minimum shores for nested terminal sets
-- statement:
--   Let G have strictly positive real vertex weights and independent terminals T. Suppose ∅⊂A⊆B⊂T, and L_A,L_B are minimum (A,T−A)- and (B,T−B)-shores. Then L_A∩L_B is a minimum (A,T−A)-shore and L_A∪L_B is a minimum (B,T−B)-shore.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - generalization: positive polynomially bounded vertex weights → arbitrary strictly positive real vertex weights; reason: no weight bound is needed in these structural claims; every source instance remains covered
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 3.4, printed p.17 (PDF p.19)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_3_4 {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (hw : Positive w) (T A B LA LB : VSet n) (hT : Independent G T)
    (hA : A.Nonempty) (hAB : A ⊆ B) (hBT : B ⊂ T)
    (hLA : IsMinShore G w A (T \ A) LA) (hLB : IsMinShore G w B (T \ B) LB) :
    IsMinShore G w A (T \ A) (LA ∩ LB) ∧ IsMinShore G w B (T \ B) (LA ∪ LB) := by sorry

end MaxIsoVertexCuts.Shredders
