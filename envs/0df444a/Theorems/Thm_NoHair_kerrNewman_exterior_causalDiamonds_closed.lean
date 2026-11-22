-- Prove2me | Theorems.Thm_NoHair_kerrNewman_exterior_causalDiamonds_closed
-- name    : NoHair.kerrNewman_exterior_causalDiamonds_closed
-- status  : Proved
-- author  : @Igor Valuev
-- created : 2026-11-22T20:19:12.155499+00:00
-- url     : https://prove2.me/theorems/2720bdae-3ef1-4f27-9646-1dce48001a77
-- title:
--   Exterior Kerr–Newman causal diamonds are closed in Cartesian spacetime
-- statement:
--   For admissible Kerr–Newman parameters, fix a time orientation and two points of the exterior $D=\{r>r_+\}$. The Cartesian Kerr–Schild image of the intrinsic causal diamond $J_D^+(p)\cap J_D^-(q)$ is closed in $\mathbb R^4$. Thus a convergent sequence in a fixed diamond has a limit in the exterior, and the two causal endpoint relations hold at the limit. Combined with a separate coordinate bound, this gives compactness of the diamond.
-- source:
--   W. Hasse and V. Perlick, A Morse-theoretical analysis of gravitational lensing by a Kerr–Newman black hole, https://arxiv.org/abs/gr-qc/0511135, section III, discussion following Eq. (12). The Cauchy surfaces there imply compact exterior diamonds, whose images in Cartesian spacetime are closed.

import Definitions.Def_NoHair_kerrNewman

open scoped ContDiff Manifold
open NoHair Set

theorem NoHair.kerrNewman_exterior_causalDiamonds_closed (m a e : ℝ)
    (hp : IsKerrNewmanBlackHoleParams m a e)
    (T : VecField (kerrNewmanSpacetime a)) (hT : IsTimeOrientation (kerrNewmanMetricField m a e) T) :
    let U := kerrNewmanSpacetime a
    let D := (Subtype.val : U → E4) ⁻¹' kerrNewmanDOC m a e
    ∀ p ∈ D, ∀ q ∈ D, IsClosed ((Subtype.val : U → E4) ''
      (causalFuture (kerrNewmanMetricField m a e) T D p ∩ causalPast (kerrNewmanMetricField m a e) T D q)) := by sorry
