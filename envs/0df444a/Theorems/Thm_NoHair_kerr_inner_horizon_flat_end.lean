-- Prove2me | Theorems.Thm_NoHair_kerr_inner_horizon_flat_end
-- name    : NoHair.kerr_inner_horizon_flat_end
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T22:54:25.512805+00:00
-- url     : https://prove2.me/theorems/0d8ea1f1-b738-4c4d-9088-ccfe1a122b01
-- title:
--   A stationary Kerr end reaching the inner horizon
-- statement:
--   In the ingoing Kerr spacetime with mass $5/2$ and rotation parameter $2$, let $A$ consist of the points with positive Kerr radius $r>1$. For Kerr–Schild time translation there exists a stationary asymptotically flat end with region exactly $A$. In particular the inner boundary of the chosen coordinate end can be the inner Killing horizon. The end uses ordinary asymptotically Cartesian coordinates at infinity, with an oblate spatial parametrization of the cutoff surface.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction, §§5 and 9, equations (32)–(38) and (88)–(94), https://arxiv.org/abs/0706.0622. The choice of an end reaching the inner horizon is a proposed counterexample using the mission's definition of a stationary asymptotically flat end.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_inner_horizon_flat_end (φ : ℝ → kerrNewmanSpacetime 2 → kerrNewmanSpacetime 2)
    (hφ : ∀ s x, (φ s x).val = x.val+s • coordBasis 0) :
    ∃ E : AsymptoticallyFlatEnd (kerrNewmanMetricField (5/2) 2 0) (kerrNewmanFieldField 2 0) φ,
      E.region = {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val} := by
  sorry
