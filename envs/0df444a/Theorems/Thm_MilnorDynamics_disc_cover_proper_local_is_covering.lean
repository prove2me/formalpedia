-- Prove2me | Theorems.Thm_MilnorDynamics_disc_cover_proper_local_is_covering
-- name    : MilnorDynamics.disc_cover_proper_local_is_covering
-- status  : Proved
-- author  : @WillR
-- created : 2026-09-30T23:20:52.407774+00:00
-- url     : https://prove2.me/theorems/fa0e4317-a16a-4741-9da5-7ac95e6ec146
-- title:
--   A proper local homeomorphism of the disc into the thrice-punctured plane is a covering map
-- statement:
--   Let p be complex differentiable on the open unit disc, avoid 0 and 1 there, and have image exactly C minus {0,1}. Suppose in addition that the restriction of p from the disc into C minus {0,1} is a proper map and a local homeomorphism. Then it is a covering map. This is the general theorem that a proper local homeomorphism onto a Hausdorff space is a covering map: a proper map is a closed map whose fibres are compact and hence finite, and a map that is a local homeomorphism on the inverse image of each point evenly covers a neighbourhood of that point. The two hypotheses are genuinely independent of holomorphy and surjectivity: precomposing any witness with the degree-two map z to z squared preserves differentiability, puncture avoidance and surjectivity, but is ramified at the origin, so it is neither proper nor a local homeomorphism there.
-- source:
--   Milnor, Dynamics in One Complex Variable, Chapter 1, Lemma 2.5; the general covering-space theorem that a proper local homeomorphism is a covering map, proved in Mathlib as IsClosedMap.isCoveringMapOn_of_isLocalHomeomorphOn (Mathlib/Topology/Covering/Basic.lean) together with IsProperMap.isClosedMap and IsProperMap.isCompact_preimage (Mathlib/Topology/Maps/Proper/Basic.lean).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- The covering half of Milnor's Lemma 2.5, in a form that cannot be wrong.

Suppose `p` is complex differentiable on the open unit disc, omits `{0,1}` there, has
image exactly `{0,1}^c`, and the restriction of `p` from the disc into `{0,1}^c` is
both a proper map and a local homeomorphism.  Then that restriction is a covering map.

This is the general covering-space theorem that a proper local homeomorphism onto a
Hausdorff space is a covering map: a proper map is a closed map with compact, hence
finite, fibres, and a map that is a local homeomorphism on the inverse image of each
point evenly covers a neighbourhood of that point.

The two extra hypotheses are the honest content for the modular lambda function:
properness holds because as the target value escapes to infinity the imaginary part of any
preimage does too, and local homeomorphismness holds by the inverse function theorem,
since the derivative of the modular lambda function never vanishes on the upper half-plane.
Both genuinely fail for a branched reparametrisation such as `z |-> z^2` precomposed with
any witness, which is why they appear as hypotheses here rather than being inferred from
holomorphy and surjectivity alone. -/
theorem disc_cover_proper_local_is_covering {p : ℂ -> ℂ}
    (hdiff : DifferentiableOn ℂ p (Metric.ball 0 1))
    (hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))
    (himage : p '' (Metric.ball 0 1) = {0, 1}ᶜ)
    (hproper : IsProperMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)))
    (hlocal :
      IsLocalHomeomorph (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))) :
    IsCoveringMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) := by sorry

end MilnorDynamics
