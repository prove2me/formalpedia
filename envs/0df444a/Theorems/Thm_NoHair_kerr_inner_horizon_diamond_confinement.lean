-- Prove2me | Theorems.Thm_NoHair_kerr_inner_horizon_diamond_confinement
-- name    : NoHair.kerr_inner_horizon_diamond_confinement
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T23:18:11.941692+00:00
-- url     : https://prove2.me/theorems/ca9c052a-4a36-47d3-bc93-281b62d245ba
-- title:
--   Compact confinement of causal diamonds above the inner Kerr horizon
-- statement:
--   For two endpoints above the inner Kerr horizon, every point of the causal diamond and connecting arcs for its two legs lie in a common compact subset of the open region. Coordinate time bounds spatial motion; in the trapped shell the radius decreases along all future causal tangents, uniformly excluding radii close to the inner horizon for arcs that reach the second endpoint.
-- source:
--   E. Minguzzi, Lorentzian causality theory, Living Reviews in Relativity 22 (2019) 3, https://doi.org/10.1007/s41114-019-0019-x. M. Visser, The Kerr spacetime: A brief introduction, https://arxiv.org/abs/0706.0622. The statements specialize causal compactness to the larger, inner-horizon-cut domain.

import Definitions.Def_NoHair_kerrNewmanTimeDirection

open NoHair Set

theorem NoHair.kerr_inner_horizon_diamond_confinement :
    let A := {x : kerrNewmanSpacetime 2 | 1 < ksRadius 2 x.val}
    let g := kerrNewmanMetricField (5/2) 2 0
    let T := kerrNewmanTimeDirection (5/2) 2 0
    ∀ p ∈ A, ∀ q ∈ A, ∃ K : Set (kerrNewmanSpacetime 2), IsCompact K ∧ K ⊆ A ∧ p ∈ K ∧ q ∈ K ∧
      ∀ x ∈ causalFuture g T A p ∩ causalPast g T A q,
        x ∈ K ∧ x ∈ causalFuture g T K p ∧ q ∈ causalFuture g T K x := by
  sorry
