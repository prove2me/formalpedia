-- Prove2me | Theorems.Thm_GaussianPerimeter_theorem1
-- name    : GaussianPerimeter.theorem1
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T11:26:30.063159+00:00
-- url     : https://prove2.me/theorems/919eae78-d2fe-4485-9369-a101107c9a16
-- title:
--   Gaussian Perimeter: theorem1
-- statement:
--   Theorem 1 of Ivanisvili and Xie, *Grokability in five inequalities*.
--
--   Source: https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/Solution.lean#L14-L20
-- source:
--   https://github.com/XinyuanXie-hub/GaussianPerimeter/blob/c54671095b3fdc672137addf46aa638c813db46a/Solution.lean#L14-L20

module
public import Definitions.Def_GaussianPerimeter_Construction
public import Definitions.Def_GaussianPerimeter_QuadratureCertificate
public import Definitions.Def_GaussianPerimeter_Solution
set_option autoImplicit true
@[expose] public section
public section
open Filter MeasureTheory
open scoped ENNReal
open GaussianPerimeter

theorem GaussianPerimeter.theorem1 :
    ENNReal.ofReal (0.31258 : ℝ) ≤
      liminf (fun n : ℕ => Γ n / ENNReal.ofReal ((n : ℝ) ^ (1 / 4 : ℝ))) atTop := by sorry
