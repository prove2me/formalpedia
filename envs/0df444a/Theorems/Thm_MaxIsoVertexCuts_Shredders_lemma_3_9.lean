-- Prove2me | Theorems.Thm_MaxIsoVertexCuts_Shredders_lemma_3_9
-- name    : MaxIsoVertexCuts.Shredders.lemma_3_9
-- status  : Open
-- author  : @Shuze Chen
-- created : 2026-11-09T23:59:41.99721+00:00
-- url     : https://prove2.me/theorems/7d2d86ac-737a-4ef4-9436-0a381e2e200b
-- title:
--   Lemma 3.9 — No minimum (A′, T\A′)-separator contains an A-outsider, for ∅ ⊂ A′ ⊆ A or ∅ ⊂ A′ ⊆ T\A
-- statement:
--   Let G have strictly positive real vertex weights, ∅⊂A⊂T, and let A′ be a nonempty subset of either A or T−A. Every minimum (A′,T−A′)-separator is disjoint from the A-outsiders with respect to T. Independence of T is not required.
--
--   Differences from the source:
--   - encoding: finite vertex sets and indexed families → Fin n vertices, Fin r indices and finite sets; reason: relabeling preserves every graph, weight, cut and certificate; indices start at zero
--   - generalization: positive polynomially bounded vertex weights → arbitrary strictly positive real vertex weights; reason: no weight bound is needed in these structural claims; every source instance remains covered
-- source:
--   Fischer and Yingchareonthawornchai, Maximal Isolating Vertex Cuts and Shredders: Structure and Applications, STOC 2027 submission (held PDF, 83 pages, SHA256 8b3a5977ae5eff3f282276ea47fc8d81c2413726a513afe04f0222c089fe1156), Lemma 3.9, printed p.20 (PDF p.22)

import Definitions.Def_MaxIsoVertexCuts_Shredders_CollectionTargets

open Classical
open scoped BigOperators
noncomputable section

namespace MaxIsoVertexCuts.Shredders

theorem lemma_3_9 {n : ℕ} (G : SimpleGraph (Fin n)) (w : Fin n → ℝ)
    (hw : Positive w) (T A A' S : VSet n) (hA : A.Nonempty) (hAT : A ⊂ T)
    (hA' : A'.Nonempty) (hsub : A' ⊆ A ∨ A' ⊆ T \ A)
    (hS : IsMinSeparator G w A' (T \ A') S) : Disjoint S (outsiders G w T A) := by sorry

end MaxIsoVertexCuts.Shredders
