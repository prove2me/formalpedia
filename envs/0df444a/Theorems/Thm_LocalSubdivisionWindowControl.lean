-- Prove2me | Theorems.Thm_LocalSubdivisionWindowControl
-- name    : LocalSubdivisionWindowControl
-- status  : Proved
-- author  : @xuanji
-- created : 2026-09-27T20:20:33.521242+00:00
-- url     : https://prove2.me/theorems/b2d88a5c-9e43-45f1-97bd-a675f032655d
-- title:
--   Local subdivision window control
-- statement:
--   For an open set U containing the carrier of a polygonal path γ and a positive tolerance δ, there is a positive radius ρ such that every same-length list sufficiently close to an anchor list whose consecutive anchor segments lie in γ has its endpoint-and-segment carrier inside U and within δ of γ.carrier.
-- source:
--   https://github.com/wpegden/crossing-consequences/blob/8769d142033fce042f502bf2857afb6b1375b5c3/Tablet/LocalSubdivisionWindowControl.lean#L1-L148

import Definitions.Def_PolygonalPath
open Classical
noncomputable section

lemma LocalSubdivisionWindowControl
    (U : Set (EuclideanSpace ℝ (Fin 2))) (γ : PolygonalPath) (δ : ℝ) :
    IsOpen U →
      γ.carrier ⊆ U →
        0 < δ →
          ∃ ρ : ℝ, 0 < ρ ∧
            ∀ anchors xs : List (EuclideanSpace ℝ (Fin 2)),
              xs.length = anchors.length →
                (∀ (i : ℕ) (hi : i + 1 < anchors.length),
                  segment ℝ anchors[i] anchors[i + 1] ⊆ γ.carrier) →
                  (∀ (i : ℕ) (hxi : i < xs.length) (hai : i < anchors.length),
                    dist xs[i] anchors[i] < ρ) →
                    (({γ.source, γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
                        {p : EuclideanSpace ℝ (Fin 2) |
                          ∃ i : ℕ, ∃ hi : i + 1 < xs.length,
                            p ∈ segment ℝ xs[i] xs[i + 1]}) ⊆ U ∧
                      (({γ.source, γ.target} : Set (EuclideanSpace ℝ (Fin 2))) ∪
                          {p : EuclideanSpace ℝ (Fin 2) |
                            ∃ i : ℕ, ∃ hi : i + 1 < xs.length,
                              p ∈ segment ℝ xs[i] xs[i + 1]}) ⊆
                        {p : EuclideanSpace ℝ (Fin 2) |
                          ∃ q : EuclideanSpace ℝ (Fin 2), q ∈ γ.carrier ∧ dist p q < δ} := by sorry
