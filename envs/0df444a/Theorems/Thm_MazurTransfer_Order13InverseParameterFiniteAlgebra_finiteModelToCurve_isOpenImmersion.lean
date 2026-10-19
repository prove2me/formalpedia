-- Prove2me | Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_finiteModelToCurve_isOpenImmersion
-- name    : MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelToCurve_isOpenImmersion
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:29:50.894766+00:00
-- url     : https://prove2.me/theorems/18fd5904-1075-4a99-b10a-1bd09cad5b9a
-- title:
--   The original inverse finite-model comparison is an open immersion
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible, and let $B=R[S][a,b]$ be the actual inverse finite coordinate algebra of the order-thirteen curve $C$. The original glued comparison $$v:\operatorname{Spec}B\longrightarrow C$$ is an open immersion. This supplies the geometric input identifying the literal inverse-chart open with the finite affine coordinate scheme.
-- source:
--   MazurTheorem, Apache-2.0, Vas and contributors. The original twelve-line finiteModelToCurve_isOpenImmersion proof from Order13InverseParameterAffineOpen.lean is retained with all original injectivity helpers. The original private overlap argument from Order13IntegralCurveProperViaHyperellipticMap.lean is explicitly included under a fresh proof namespace, with its original copyright and attribution. Two references to the ordinary localization are fully qualified to avoid an ambiguous native alias. Original and public full closed types are kernel-compared. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: original inverse affine-chart isomorphism and actual integral FiniteMapData.

import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseFiniteModelToCurve
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13InverseParameterFiniteAlgebra
universe u

theorem MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelToCurve_isOpenImmersion (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    IsOpenImmersion (finiteModelToCurve R h104)  := by sorry
