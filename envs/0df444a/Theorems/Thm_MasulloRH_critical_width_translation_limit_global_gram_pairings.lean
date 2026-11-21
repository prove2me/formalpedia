-- Prove2me | Theorems.Thm_MasulloRH_critical_width_translation_limit_global_gram_pairings
-- name    : MasulloRH.critical_width_translation_limit_global_gram_pairings
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:30:03.720062+00:00
-- url     : https://prove2.me/theorems/fc7a6fdb-7243-4299-8b01-fad46bfe42ab
-- title:
--   Critical-width translation limit for global weighted Gram pairings
-- statement:
--   In the actual critical-width radial weight w(x)=exp(|x|)(1+x²)², translating both arguments of a fixed weighted Gram pairing and normalizing by exp(L)L⁴ gives the Gram pairing for exp(x)dx. The assertion holds for every complex measurable product g with w|g| integrable, hence for arbitrary pairs of weighted square-integrable vectors. No band or theta projection is assumed.
-- source:
--   Masullo (9.2.2.41); critical-width large-translation asymptotics for the global Gram form.

import Mathlib
open MeasureTheory Filter Topology

theorem MasulloRH.critical_width_translation_limit_global_gram_pairings (g : ℝ → ℂ) (hg : AEStronglyMeasurable g volume) :
    let w : ℝ → ℝ := fun x => Real.exp |x| * (1 + x^2)^2
    Integrable (fun x => w x * ‖g x‖) →
    Tendsto (fun L : ℝ => ∫ x : ℝ, (w (x+L) / (Real.exp L * L^4)) • g x)
      atTop (𝓝 (∫ x : ℝ, Real.exp x • g x)) := by sorry
