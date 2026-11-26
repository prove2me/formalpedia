-- Prove2me | Theorems.Thm_GeodesicIsPiecewiseGeodesic
-- name    : GeodesicIsPiecewiseGeodesic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:14.184965+00:00
-- url     : https://prove2.me/theorems/49781022-4452-4515-b5ad-30668181f76e
-- title:
--   Geodesic Is Piecewise Geodesic: Geodesic Is Piecewise Geodesic
-- statement:
--   A geodesic pairing's chosen geodesic `G x y` is piecewise geodesic with exactly one edge
--   (paper.tex line 1441 / the surrounding discussion of `\hat\gamma_{i,l}` and `\bar\gamma_{i,l}`
--   being built from geodesics `G_{x,y}`, which the paper treats as visibly piecewise-geodesic).
--
--   Source: https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/GeodesicIsPiecewiseGeodesic.lean#L10-L27
-- source:
--   https://github.com/Inspectordaniel/metric-surgery-lean/blob/91c2fc65884c9b284fdc6ba4071aa63c12ded471/Tablet/GeodesicIsPiecewiseGeodesic.lean#L10-L27

import Definitions.Def_Tablet_GeodesicPairing
import Definitions.Def_Tablet_IsPiecewiseGeodesicWith
import Definitions.Def_Tablet_GeodesicIsPiecewiseGeodesic
set_option autoImplicit false
open Set

theorem GeodesicIsPiecewiseGeodesic {E : Type*} [MetricSpace E] (GP : GeodesicPairing E)
    (x y : E) : IsPiecewiseGeodesicWith (GP.G x y) 1 := by sorry
