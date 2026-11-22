-- Prove2me | Theorems.Thm_NoHair_kerrNewman_exterior_compactLimitCurve
-- name    : NoHair.kerrNewman_exterior_compactLimitCurve
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:43:24.676445+00:00
-- url     : https://prove2.me/theorems/46e8d6cc-84d5-4d89-a5cb-f8bb00226bd7
-- title:
--   Causal endpoint limits in a compact part of the Kerr–Newman exterior
-- statement:
--   Let $K$ be a compact subset of the positive-radius Kerr–Newman exterior $D$. If the endpoints of causal segments contained in $K$ converge, the limiting events are causally related in $D$. Both the approximating and the resulting relation use the mission’s $C^1$ future causal curves, with equality of endpoints allowed. The time orientation is arbitrary.
-- source:
--   E. Minguzzi, Limit curve theorems in Lorentzian geometry, J. Math. Phys. 49 (2008) 092501, https://arxiv.org/abs/0712.0390. For passage from a causal limit curve to a piecewise-geodesic witness and smooth causal representatives see E. Minguzzi, Lorentzian causality theory, Living Rev. Relativ. 22 (2019) 3, https://doi.org/10.1007/s41114-019-0019-x.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set

theorem NoHair.kerrNewman_exterior_compactLimitCurve (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let g := kerrNewmanMetricField m a e
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    ∀ K : Set U, IsCompact K → K ⊆ D →
      closure {z : U × U | z.1 ∈ K ∧ z.2 ∈ K ∧ z.2 ∈ causalFuture g T K z.1} ⊆
        {z : U × U | z.2 ∈ causalFuture g T D z.1} := by sorry
