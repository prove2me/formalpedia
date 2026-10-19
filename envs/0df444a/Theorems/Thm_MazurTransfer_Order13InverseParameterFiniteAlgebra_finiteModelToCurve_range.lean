-- Prove2me | Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_finiteModelToCurve_range
-- name    : MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelToCurve_range
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:29:09.166611+00:00
-- url     : https://prove2.me/theorems/ce83ea0c-ee12-477a-b438-1cef87bbde80
-- title:
--   The original inverse finite-model comparison has its specified two-chart image
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $v:\operatorname{Spec}B\to C$ be the original glued comparison from the actual inverse finite coordinate algebra to the order-thirteen curve. Its image is exactly the union of the specified ordinary-parameter and positive-reciprocal chart images: $$\operatorname{im}(v)=\operatorname{im}(v_{\mathrm{ord}})\cup\operatorname{im}(v_{\mathrm{rec}}).$$ This identifies the underlying subset used by the actual inverse affine-chart presentation.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. The seventeen-line original finiteModelToCurve_range proof from Order13InverseParameterGlobalComparison.lean is unchanged. Its project import is the public glued-morphism definition and original chart restriction identities. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: original inverse affine-chart isomorphism and actual integral FiniteMapData.

import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseFiniteModelToCurve
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13InverseParameterFiniteAlgebra
universe u

theorem MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelToCurve_range (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    Set.range (finiteModelToCurve R h104) =
      Set.range (ordinaryParameterCurveMap R) ∪ Set.range (positiveReciprocalCurveMap R)  := by sorry
