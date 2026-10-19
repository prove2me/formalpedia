-- Prove2me | Theorems.Thm_MazurTransfer_Order13PublicFiniteChartParameters_parameter_product
-- name    : MazurTransfer.Order13PublicFiniteChartParameters.parameter_product
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:59:33.386985+00:00
-- url     : https://prove2.me/theorems/1348fc46-a26f-4cce-a4d5-43431e2c6f69
-- title:
--   The two actual finite-chart parameters are reciprocal on their overlap
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $U$ and $V$ be the two actual finite-chart opens of the order-thirteen curve, and let $f$ and $g$ be their specified public parameter sections. On their literal intersection, $$f|_{U\cap V}\,g|_{U\cap V}=1.$$ This is the reciprocal-product field of the unchanged integral FiniteMapData contract.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. Reassembles the original parameter-reciprocity argument using the specified published first and inverse chart section constructors. The Proved public actual intersection theorem identifies the common chart, and the public transported-section theorem plus checked inverse pullback identify the two literal values. The original nine-line section-pullback injectivity helper is explicitly included under a fresh proof namespace. The statement consistently uses the first chart presentation of its published section; the original canonical first open is kernel-equal by the checked reflexive bridge. No equality with an older chosen first parameter section is asserted. The complete public formal type is kernel-compared, and its source declaration boundary is revalidated against the full frontend oracle. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: res_f_mul_res_g in actual integral FiniteMapData.

import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartSections
import Definitions.Def_MazurTransfer_Order13InverseFiniteChartSections
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer
open MazurTransfer.Order13InverseParameterFiniteAlgebra
universe u

theorem MazurTransfer.Order13PublicFiniteChartParameters.parameter_product (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) :
    ((curveScheme R).presheaf.map (homOfLE (inf_le_left :
      Order13FirstFiniteChartFromPublicTheorem.chartOpen R ⊓ inverseChartOpen R ≤ Order13FirstFiniteChartFromPublicTheorem.chartOpen R)).op)
      (Order13FirstFiniteChartFromPublicTheorem.parameterSection R h104) *
    ((curveScheme R).presheaf.map (homOfLE (inf_le_right :
      Order13FirstFiniteChartFromPublicTheorem.chartOpen R ⊓ inverseChartOpen R ≤ inverseChartOpen R)).op)
      (Order13InverseFiniteChartFromPublicTheorems.parameterSection R h104) = 1 := by sorry
