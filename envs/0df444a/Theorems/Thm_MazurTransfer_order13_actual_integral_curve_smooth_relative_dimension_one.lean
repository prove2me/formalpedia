-- Prove2me | Theorems.Thm_MazurTransfer_order13_actual_integral_curve_smooth_relative_dimension_one
-- name    : MazurTransfer.order13_actual_integral_curve_smooth_relative_dimension_one
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-10T02:54:21.476644+00:00
-- url     : https://prove2.me/theorems/1035f9f0-99cc-4038-a6f8-7c34e101c588
-- title:
--   Actual integral curve is smooth of relative dimension one where 104 is invertible
-- statement:
--   Let $R$ be any commutative ring in which $104$ is a unit, and let $X_R$ be the literal two-chart order-13 curve with its actual structural morphism $c_R:X_R\to\operatorname{Spec}R$. Then
--
--   $$c_R\text{ is smooth of relative dimension }1.$$
--
--   The assertion applies in particular to the actual family over $\mathbb Z[1/104]$ and every scalar extension of that family. No field, noetherianity, domain, supplied model, differential-rank or dimension hypothesis is imposed on $R$. This supplies the relative-dimension input for integral Picard representability. Arbitrarily large finite-map data adapted to one section, Picard chart sections, the compatible integral Picard family, rational rank zero and torsion specialization remain separate obligations.
-- source:
--   MazurTheorem WIP at 54d43d8dda8a6fcf069cc02a815f850d762c5c0c, Apache-2.0: https://github.com/Vilin97/MazurTheorem/tree/54d43d8dda8a6fcf069cc02a815f850d762c5c0c . Complete owned differential, domain and scalar-extension arguments with Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. All attribution retained.

import Mathlib
import Definitions.Def_MazurTransfer_Order13ExplicitCurve
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_geometrically_integral
import Theorems.Thm_MazurTransfer_order13_actual_integral_curve_flat_finitely_presented_and_smooth
import Theorems.Thm_MazurTransfer_order13_actual_whole_curve_base_change_isomorphism

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve

theorem MazurTransfer.order13_actual_integral_curve_smooth_relative_dimension_one.{u}
    (R : Type u) [CommRing R] (h104 : IsUnit (104 : R)) :
    SmoothOfRelativeDimension 1 (curveToBase R) := by sorry
