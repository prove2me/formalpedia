-- Prove2me | Theorems.Thm_MilnorDynamics_disc_cover_of_proper_local_homeo
-- name    : MilnorDynamics.disc_cover_of_proper_local_homeo
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T22:57:07.134289+00:00
-- url     : https://prove2.me/theorems/56469e78-be13-4769-8650-221a0d164796
-- title:
--   A proper local homeomorphism of the disc into the thrice-punctured plane is a covering map
-- statement:
--   Let p be complex differentiable on the open unit disc, avoid 0 and 1 there, and have image exactly C minus {0,1}. Suppose in addition that the restriction of p from the disc into C minus {0,1} is a proper map and a local homeomorphism. Then it is a covering map. This is the standard theorem that a proper local homeomorphism from a Hausdorff space to a Hausdorff space is a covering map, realised on the platform as the Proved theorem Erdos1041.Counterexample.s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph (7fc40c8f-97fe-4a2d-a074-ce2bc3873cc5). The two hypotheses are genuinely independent of holomorphy and surjectivity: precomposing any witness with the degree-two map z to z squared preserves differentiability, puncture avoidance and surjectivity, but is ramified at the origin, so it is neither proper nor a local homeomorphism there.
-- source:
--   Milnor, Dynamics in One Complex Variable, Chapter 1, Lemma 2.5; the general covering-space theorem that a proper local homeomorphism is a covering map, realised on the platform as the Proved theorem Erdos1041.Counterexample.s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph (7fc40c8f-97fe-4a2d-a074-ce2bc3873cc5).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set Topology

namespace MilnorDynamics

/-- The covering half of Milnor's Lemma 2.5, in a form that cannot be wrong.

Suppose `p` is complex differentiable on the open unit disc, omits `{0,1}` there, has
image exactly `{0,1}^c`, and the restriction of `p` from the disc into `{0,1}^c` is
both a proper map and a local homeomorphism.  Then that restriction is a covering map.

This is exactly the general theorem that a proper local homeomorphism onto a Hausdorff
space is a covering map, which the platform already has as the `Proved` theorem
`Erdos1041.Counterexample.s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph`
(7fc40c8f-97fe-4a2d-a074-ce2bc3873cc5), and it is the content of
`MilnorDynamics.disc_cover_proper_and_local_exists`.

The two extra hypotheses are the honest content for the modular lambda function:
properness holds because as the target value escapes to infinity the imaginary part of
any preimage does too, and local homeomorphismness holds by the inverse function
theorem, since the derivative of the modular lambda function never vanishes on the
upper half-plane.  Both genuinely fail for a branched reparametrisation such as
`z |-> z^2` precomposed with any witness, which is why they must appear as hypotheses
here rather than being inferred from holomorphy and surjectivity alone. -/
theorem disc_cover_of_proper_local_homeo {p : ℂ -> ℂ}
    (hdiff : DifferentiableOn ℂ p (Metric.ball 0 1))
    (hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))
    (himage : p '' (Metric.ball 0 1) = {0, 1}ᶜ)
    (hproper : IsProperMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)))
    (hlocal :
      IsLocalHomeomorph (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))) :
    IsCoveringMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) := by sorry

end MilnorDynamics
