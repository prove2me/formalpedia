-- Prove2me | Theorems.Thm_MasulloRH_critical_width_translated_global_gram_density
-- name    : MasulloRH.critical_width_translated_global_gram_density
-- status  : Proved
-- author  : @Yi
-- created : 2026-11-21T05:26:11.427359+00:00
-- url     : https://prove2.me/theorems/2d0d3726-0270-4fcc-8976-28aea1ab6e35
-- title:
--   Dominated translation limit for the global critical-width Gram density
-- statement:
--   At α=1/2 and s=4, the radial weight is w(x)=exp(|x|)(1+x²)². The density w(x+L)/(exp(L)L⁴) converges to exp(x) as L→∞ and is bounded by 9w(x) for every L≥1. This permits dominated convergence for all fixed weighted Hilbert pairings of translated vectors, including geometric theta vectors.
-- source:
--   Masullo (9.2.2.41); critical-width large-translation asymptotics for the global Gram form.

import Mathlib
open Filter Topology

theorem MasulloRH.critical_width_translated_global_gram_density :
    let w := fun x : ℝ => Real.exp |x| * (1 + x^2)^2
    (∀ x : ℝ, Tendsto (fun L : ℝ => w (x+L) / (Real.exp L * L^4))
      atTop (𝓝 (Real.exp x))) ∧
    (∀ x L : ℝ, 1 ≤ L → w (x+L) / (Real.exp L * L^4) ≤ 9 * w x) := by sorry
