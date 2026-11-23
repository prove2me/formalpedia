-- Prove2me | Theorems.Thm_NoHair_complete_static_double_from_reflection_and_point_chart
-- name    : NoHair.complete_static_double_from_reflection_and_point_chart
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-23T10:51:06.137131+00:00
-- url     : https://prove2.me/theorems/c3f8689d-d2cb-4c12-90ff-c79f6d6182b0
-- title:
--   Fill a reflected static double using its smooth negative-end chart
-- statement:
--   Attach the center of the negative-end chart to the smooth double. The compact truncated core, regular metric across the added point, and lower length bound on the remaining end ensure completeness. The surviving end retains its zero ADM flux. Transfer the signed lapse and physical chart across the open inclusion.
-- source:
--   P. T. Chruściel, The classification of static vacuum space-times containing an asymptotically flat spacelike hypersurface with compact interior, Class. Quantum Grav. 16 (1999) 661–687, Proposition 3.3 and the static equations (5.4)–(5.6), https://homepage.univie.ac.at/piotr.chrusciel/papers/chrusciel/static.pdf. Bunting and Masood-ul-Alam, Gen. Relativ. Gravit. 19 (1987) 147–154, https://doi.org/10.1007/BF00770326.

import Definitions.Def_NoHair_staticReflectionAndCap

open NoHair Set Filter Bundle
open scoped ContDiff Manifold Topology

theorem NoHair.complete_static_double_from_reflection_and_point_chart (Ω W : Set ADMPoint) (N : ADMPoint → ℝ) (h : ADMPoint → Matrix (Fin 3) (Fin 3) ℝ)
    (c : RegularRiemannianStaticEnd Ω W N h)
    (d : ReflectedStaticDouble Ω N h) (a : StaticMinusPointChart Ω N h)
    (hcompact : ∀ R : ℝ, IsCompact ((d.inc true '' {x : ↥(closure Ω) | R < ‖x.val‖}) ∪ (d.inc false '' {x : ↥(closure Ω) | R < ‖x.val‖}))ᶜ)
    (hpositiveEnd : ∃ R : ℝ, 0 < R ∧
      (∀ x : ADMPoint, R < ‖x‖ → ∀ v : ADMPoint, ‖v‖^2 / 4 ≤
        ∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h x i j * v i * v j) ∧
      ∀ (γ : ℝ → ADMPoint) (a b : ℝ), a ≤ b → ContDiff ℝ 1 γ →
        (∀ t ∈ Set.Icc a b, R < ‖γ t‖) →
        ‖γ b - γ a‖ ≤ 2 * ∫ t in a..b, Real.sqrt
          (∑ i : Fin 3, ∑ j : Fin 3, staticPositiveMetric N h (γ t) i j * deriv γ t i * deriv γ t j))
    (hmass : Tendsto (staticADMFlux (staticPositiveMetric N h)) atTop (𝓝 0)) :
    Nonempty (StaticConformalCompletion Ω N h) := by sorry
