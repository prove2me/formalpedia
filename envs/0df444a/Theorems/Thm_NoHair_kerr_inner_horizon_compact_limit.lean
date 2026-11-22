-- Prove2me | Theorems.Thm_NoHair_kerr_inner_horizon_compact_limit
-- name    : NoHair.kerr_inner_horizon_compact_limit
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T23:18:01.969825+00:00
-- url     : https://prove2.me/theorems/ce9fab0b-3315-4671-9fbf-23d6ff095e80
-- title:
--   Limits of causal arcs confined above the inner Kerr horizon
-- statement:
--   For a compact subset of the Kerr region above the inner horizon, limits of pairs joined by a future-directed causal arc within that compact set are joined by a regular causal arc in the open region. The canonical ingoing time orientation is used.
-- source:
--   E. Minguzzi, Lorentzian causality theory, Living Reviews in Relativity 22 (2019) 3, https://doi.org/10.1007/s41114-019-0019-x. M. Visser, The Kerr spacetime: A brief introduction, https://arxiv.org/abs/0706.0622. The statements specialize causal compactness to the larger, inner-horizon-cut domain.

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set

theorem NoHair.kerr_inner_horizon_compact_limit :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    ∀ K : Set (kerrNewmanSpacetime 2), IsCompact K → K ⊆ A →
      closure {z : (kerrNewmanSpacetime 2) × (kerrNewmanSpacetime 2) |
        z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1} ⊆
        {z | z.2 ∈ causalFuture g T A z.1} := by
  sorry
