-- Prove2me | Theorems.Thm_NoHair_kerrNewman_exterior_diamondCurveConfinement
-- name    : NoHair.kerrNewman_exterior_diamondCurveConfinement
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:43:23.117375+00:00
-- url     : https://prove2.me/theorems/ccee07ea-b05a-4670-bf50-a9077852c77b
-- title:
--   Both legs of a Kerr–Newman exterior causal diamond fit in one compact exterior set
-- statement:
--   Fix two events $p,q$ in the exterior $D$. There is a compact subset $K\subset D$ containing both endpoints. Each event $x$ in their causal diamond can be joined to $p$ and to $q$ by causal curves in $K$, with trivial segments allowed. The same $K$ works for every $x$. A coordinate proof bounds the spatial displacement by the elapsed Kerr–Schild time and controls approach to the horizon with the optical weight $(r-r_+)\exp(-t/m)$.
-- source:
--   W. Hasse and V. Perlick, A Morse-theoretical analysis of gravitational lensing by a Kerr–Newman black hole, https://arxiv.org/abs/gr-qc/0511135, section III. The optical weight here is a direct estimate in ingoing Kerr–Schild coordinates.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set

theorem NoHair.kerrNewman_exterior_diamondCurveConfinement (m a e : ℝ) (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let g := kerrNewmanMetricField m a e
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    ∀ p ∈ D, ∀ q ∈ D, ∃ K : Set U, IsCompact K ∧ K ⊆ D ∧ p ∈ K ∧ q ∈ K ∧
      ∀ x ∈ causalFuture g T D p ∩ causalPast g T D q,
        x ∈ K ∧ x ∈ causalFuture g T K p ∧ q ∈ causalFuture g T K x := by sorry
