-- Prove2me | Theorems.Thm_MilnorDynamics_disk_cover_proper_and_local
-- name    : MilnorDynamics.disk_cover_proper_and_local
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T21:27:44.592986+00:00
-- url     : https://prove2.me/theorems/8e3e5e9d-3933-4171-9c8e-65cc733cdfdc
-- title:
--   The disc covering of the thrice-punctured sphere is proper and a local homeomorphism
-- statement:
--   Let p from D to C minus {0,1} be the covering obtained from the modular function. Two analytic facts about p turn it into a covering map. First, p is proper: as the modulus of w tends to infinity in the target, the imaginary part of the preimage tends to infinity, so the preimage of a compact subset of C minus {0,1} is a compact subset of D. Second, p is a local homeomorphism: it is complex differentiable and its derivative is the derivative of the modular lambda function, which never vanishes on H; by the inverse function theorem for complex analytic maps, p is then a biholomorphism onto a neighbourhood of each of its values. A proper local homeomorphism onto a Hausdorff space is a covering map, so these two estimates discharge the covering-map obligation in Milnor's Lemma 2.5.
-- source:
--   Milnor, Dynamics in One Complex Variable, Chapter 1, Lemma 2.5; the inverse function theorem for holomorphic functions (derivative nonzero) and the standard properness estimate for the modular lambda function. The closing step is the general theorem that a proper local homeomorphism onto a Hausdorff space is a covering map, available on the platform as the Proved theorem Erdos1041.Counterexample.s2_isCoveringMap_of_isProperMap_of_isLocalHomeomorph (7fc40c8f-97fe-4a2d-a074-ce2bc3873cc5).

import Mathlib
import Definitions.Def_MilnorDynamics_NormalFamilies

open scoped OnePoint
open Filter Set

namespace MilnorDynamics

/-- The two analytic estimates that turn the disc covering of the thrice-punctured sphere
into a covering map.  Let `p : D -> C \ {0,1}` be the covering furnished by the modular
function.  Then `p` is proper (preimages of compact sets are compact) and a local
homeomorphism (it is holomorphic with nonvanishing derivative, since the derivative of the
modular lambda function never vanishes on `H`).  Together these imply `IsCoveringMap p` by
the general theorem that a proper local homeomorphism from a Hausdorff space is a covering
map. -/
theorem disk_cover_proper_and_local {p : ℂ → ℂ}
    (hp : MapsTo p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ))
    (hdiff : DifferentiableOn ℂ p (Metric.ball 0 1)) :
    IsProperMap (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) ∧
      IsLocalHomeomorph (hp.restrict p (Metric.ball 0 1) ({0, 1}ᶜ : Set ℂ)) := by sorry

end MilnorDynamics
