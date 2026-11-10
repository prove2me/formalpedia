-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_3_5
-- name    : MaxIsoVertexCuts.Shredders.lemma_3_5
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:59:26.92919+00:00
-- url     : https://prove2.me/theorems/41db3379-7056-41b0-8e3b-c5da5426061e
-- title:
--   Lemma 3.5 — Differences L_A \ N[L_B] and L_B \ N[L_A] of minimum shores are minimum shores
-- statement:
--   Let G have strictly positive real vertex weights, independent terminals T, and disjoint nonempty proper subsets A,B of T. If L_A,L_B are minimum shores for their respective terminal bipartitions, then L_A−N[L_B] and L_B−N[L_A] are minimum shores for the same respective bipartitions.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - generalization: positive polynomially bounded vertex weights → arbitrary strictly positive real vertex weights; reason: no weight bound is needed in these structural claims; every source instance remains covered
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 3.5, printed p.18 (PDF p.20)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_3_5 {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (hw : Positive w) (T A B LA LB : VSet n) (hT : Independent G T)
    (hA : A.Nonempty) (hB : B.Nonempty) (hAT : A ⊂ T) (hBT : B ⊂ T) (hAB : Disjoint A B)
    (hLA : IsMinShore G w A (T \ A) LA) (hLB : IsMinShore G w B (T \ B) LB) :
    IsMinShore G w A (T \ A) (LA \ closedNbhd G LB) ∧
    IsMinShore G w B (T \ B) (LB \ closedNbhd G LA) := by sorry

end MaxIsoVertexCuts.Shredders
