-- Prove2me | Theorems.Thm_NoHair_kerr_oblate_chart_component_decay
-- name    : NoHair.kerr_oblate_chart_component_decay
-- status  : Open
-- author  : @Igor Valuev
-- created : 2026-11-22T23:24:05.051584+00:00
-- url     : https://prove2.me/theorems/5aa5a4ce-2fca-47e8-94a8-d9705d3db435
-- title:
--   Cartesian falloff after the oblate Kerr coordinate change
-- statement:
--   The stationary oblate coordinate map sends a spatial point $Rn$ to $(Rn_1-2n_2,Rn_2+2n_1,Rn_3)$. For mass $5/2$ and spin $2$, all pulled-back Kerr metric coefficients differ from their Minkowski values by $O(R^{-1})$, and all their Cartesian first derivatives are $O(R^{-2})$, uniformly for $R>1$.
-- source:
--   M. Visser, The Kerr spacetime: A brief introduction (2007), Cartesian Kerr–Schild and oblate coordinates, https://arxiv.org/abs/0706.0622. The bounds follow by differentiation in inverse spatial radius and normalized Cartesian direction.

import Definitions.Def_NoHair_kerrNewman

open NoHair Set
open scoped ContDiff Manifold

theorem NoHair.kerr_oblate_chart_component_decay (ψ : E4 → kerrNewmanSpacetime 2)
    (hψ : ∀ y ∈ exteriorRegion 1, (ψ y).val = WithLp.toLp 2
      ![y 0, y 1-2*(y 2/spatialRadius y), y 2+2*(y 1/spatialRadius y), y 3]) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y ∈ exteriorRegion 1, ∀ i j : Fin 4,
      |pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ y i j - minkowski i j| ≤ C / spatialRadius y ∧
      ∀ k : Fin 4, |coordPartial (fun z => pullbackCoeffs (kerrNewmanMetricField (5/2) 2 0) ψ z i j) k y| ≤
        C / spatialRadius y ^ 2 := by
  sorry
