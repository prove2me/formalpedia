-- Prove2me | Theorems.Thm_MazurTransfer_Order13InverseFiniteChartFromPublicTheorems_parameter_basicOpen
-- name    : MazurTransfer.Order13InverseFiniteChartFromPublicTheorems.parameter_basicOpen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:55:24.50312+00:00
-- url     : https://prove2.me/theorems/d6083dff-abf9-4d8b-8380-29235bae8f53
-- title:
--   The actual inverse parameter cuts out the ordinary parameter open
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $V$ be the actual inverse finite chart of the order-thirteen curve $C$ and $g$ its specified inverse parameter section. Its basic open is exactly the original ordinary parameter-localization image: $$D_V(g)=\operatorname{im}\bigl(\operatorname{Spec}(A_t)\to C\bigr).$$ This is the inverse parameter basic-open field used by integral FiniteMapData.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. The original inverse basic-open transport argument is retained for the actual public inverse affine-open presentation and specified inverse parameter section. Uses the Proved public generic basic-open transport theorem and the original published finite-atlas image and gluing-restriction identities. The complete public formal type is compared in the kernel with the checked solution and has no unresolved term or universe parameters. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: actual integral FiniteMapData.

import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseFiniteChartSections
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
universe u

theorem MazurTransfer.Order13InverseFiniteChartFromPublicTheorems.parameter_basicOpen (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) :
    (curveScheme R).basicOpen (MazurTransfer.Order13InverseFiniteChartFromPublicTheorems.parameterSection R h104) =
      (MazurTransfer.Order13InverseParameterFiniteAlgebra.ordinaryParameterCurveMap R).opensRange := by sorry
