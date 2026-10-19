-- Prove2me | Theorems.Thm_MazurTransfer_Order13FirstFiniteChartFromPublicTheorem_parameter_basicOpen
-- name    : MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.parameter_basicOpen
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:54:36.989685+00:00
-- url     : https://prove2.me/theorems/3bca0d4e-71fb-42d2-83d3-a8d5aa1fee59
-- title:
--   The actual first parameter cuts out the ordinary parameter open
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $U$ be the actual first finite chart of the order-thirteen curve $C$, and let $f$ be the specified parameter section constructed from its selected public affine presentation. Its basic open is exactly the original ordinary parameter-localization image: $$D_U(f)=\operatorname{im}\bigl(\operatorname{Spec}(A_t)\to C\bigr).$$ This is the first parameter basic-open field used by integral FiniteMapData.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. A direct proof using the already Proved public ordinary-localization theorem, its literal coordinate-inclusion compatibility, the selected public first-chart presentation and the Proved generic basic-open transport theorem. The ring equivalence underlying the public algebra equivalence is projected with its actual instance arguments retained. The chosen first-chart presentation and parameter section are those of the published constructor; no equality with an older chosen parameter section is asserted. The complete public formal type is compared in the kernel with the checked solution and has no unresolved term or universe parameters. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: actual integral FiniteMapData.

import Mathlib
import Definitions.Def_MazurTransfer_Order13FirstFiniteChartSections
import Definitions.Def_MazurTransfer_Order13InverseChartOpen
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
universe u

theorem MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.parameter_basicOpen (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) :
    (curveScheme R).basicOpen (MazurTransfer.Order13FirstFiniteChartFromPublicTheorem.parameterSection R h104) =
      (MazurTransfer.Order13InverseParameterFiniteAlgebra.ordinaryParameterCurveMap R).opensRange := by sorry
