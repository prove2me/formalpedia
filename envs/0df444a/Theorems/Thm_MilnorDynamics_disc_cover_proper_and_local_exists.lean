-- Prove2me | Theorems.Thm_MilnorDynamics_disc_cover_proper_and_local_exists
-- name    : MilnorDynamics.disc_cover_proper_and_local_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T22:56:47.287636+00:00
-- url     : https://prove2.me/theorems/3efd79e3-513f-47b9-802e-7c041c78a7b6
-- title:
--   The modular lambda covering of the disc is proper and a local homeomorphism
-- statement:
--   There is a map p from the open unit disc into the twice-punctured plane, obtained by composing the modular lambda function with the Cayley bijection from the disc to the upper half-plane, such that the restriction of p from the disc into C minus {0,1} is a proper map and a local homeomorphism, and p has image exactly C minus {0,1}. Properness: as the target value escapes to infinity, the imaginary part of any preimage does too, so the preimage of a compact subset of C minus {0,1} is a compact subset of the disc. Local homeomorphismness: p is holomorphic and its derivative, being the derivative of the modular lambda function, never vanishes on the upper half-plane (its only zeros are the cusps, which lie on the boundary), so the inverse function theorem for holomorphic functions makes p a biholomorphism onto a neighbourhood of each of its values. These two estimates are exactly what turns the lambda map into a covering map; they are the content of Milnor's Lemma 2.5.
-- source:
--   Milnor, Dynamics in One Complex Variable, Chapter 1, Lemma 2.5; the inverse function theorem for holomorphic functions applied to the modular lambda function, whose derivative is nonvanishing on the upper half-plane; the standard properness estimate that the j-invariant tends to infinity as the imaginary part does. The closing step, that a proper local homeomorphism is a covering map, is the Proved theorem Erdos1041.Counterexample.s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph (7fc40c8f-97fe-4a2d-a074-ce2bc3873cc5).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- The two analytic estimates that make the modular lambda covering a covering map.

There is a map `p`, the modular lambda function pulled back to the disc by the Cayley
bijection, which is complex differentiable on the open unit disc, omits `{0,1}` there,
has image exactly `{0,1}^c`, and whose restriction from the disc into `{0,1}^c` is a
proper map and a local homeomorphism.

Properness holds because `|j|` tends to infinity as the imaginary part of the preimage
does, so the preimage of a compact subset of `{0,1}^c` is a compact subset of the disc.
Local homeomorphismness holds by the inverse function theorem for holomorphic functions,
since the derivative of the modular lambda function never vanishes on the upper
half-plane: its only zeros are the cusps, which lie on the boundary of the half-plane.
Composing with the Cayley homeomorphism, a biholomorphism from the disc onto the upper
half-plane, transports both properties to the disc. -/
theorem disc_cover_proper_and_local_exists :
    exists p : ℂ -> ℂ, DifferentiableOn ℂ p (Metric.ball 0 1) /\
      exists hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ),
        p '' (Metric.ball 0 1) = {0, 1}ᶜ /\
          IsProperMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) /\
            IsLocalHomeomorph
              (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) := by sorry

end MilnorDynamics
