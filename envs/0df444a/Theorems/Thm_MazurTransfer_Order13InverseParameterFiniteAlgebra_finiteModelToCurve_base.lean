-- Prove2me | Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_finiteModelToCurve_base
-- name    : MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelToCurve_base
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:30:57.871617+00:00
-- url     : https://prove2.me/theorems/f87b3c8a-ab89-47c2-b48f-2ffc1cacbe59
-- title:
--   The original inverse finite-model comparison preserves the structural base map
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $B=R[S][a,b]$ be the actual inverse finite coordinate algebra and $v:\operatorname{Spec}B\to C$ the original glued comparison to the order-thirteen curve. Let $c:C\to\operatorname{Spec}R$ and $b:\operatorname{Spec}B\to\operatorname{Spec}R$ be their specified structural maps. Then $$c\circ v=b.$$ This compatibility supplies the actual $R$-algebra comparison for the inverse affine-chart section ring.
-- source:
--   Original thirteen-line finiteModelToCurve_base proof from MazurTheorem Order13InverseParameterCurveFiniteMap.lean, Apache-2.0, Vas and contributors. Three original proof-only helpers are explicitly included under a fresh namespace to avoid dependence on transitive native-cache helpers. The two chart base comparisons additionally unfold the kernel-equal public aliases for the finite affine scheme and parameter map. The original final proof body, structural morphisms and all hypotheses are retained. Original and public closed types are kernel-compared. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: inverse affine-open structural R-algebra section comparison and actual integral FiniteMapData.

import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseFiniteModelToCurve
import Definitions.Def_MazurTransfer_Order13InverseFiniteModelBaseMaps
open CategoryTheory AlgebraicGeometry
open MazurTorsion.XOneThirteenProjectiveCurve
open MazurTransfer.Order13InverseParameterFiniteAlgebra
universe u

theorem MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteModelToCurve_base (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R] (h104 : IsUnit (104 : R)) :
    finiteModelToCurve R h104 ≫ curveToBase R = inverseFiniteAffineSchemeToBase R  := by sorry
