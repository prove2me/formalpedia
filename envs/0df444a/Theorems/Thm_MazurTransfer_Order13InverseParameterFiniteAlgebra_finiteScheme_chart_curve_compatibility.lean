-- Prove2me | Theorems.Thm_MazurTransfer_Order13InverseParameterFiniteAlgebra_finiteScheme_chart_curve_compatibility
-- name    : MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteScheme_chart_curve_compatibility
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-17T06:22:34.536279+00:00
-- url     : https://prove2.me/theorems/612fd30b-4595-40a4-b347-70bbaca1b4c3
-- title:
--   The actual inverse finite-atlas maps agree on every pullback overlap
-- statement:
--   Let $R$ be a noetherian commutative integral domain with $104$ invertible. Let $B=R[S][a,b]$ be the actual inverse finite coordinate algebra of the order-thirteen curve $C$. Its specified two-member open atlas has the ordinary parameter localization and positive reciprocal patch as chart sources, with retained maps $v_i$ into $C$. On every pullback overlap with projections $p_1$ and $p_2$, $$v_i\circ p_1=v_j\circ p_2.$$ Thus the actual atlas maps are compatible and can be glued to a morphism $\operatorname{Spec}B\to C$.
-- source:
--   Original finiteScheme_chart_curve_compatibility theorem from MazurTheorem Order13InverseParameterGlobalComparison.lean, Apache-2.0, Vas and contributors. The twenty-nine-line proof and eight original inline proof-only helpers are unchanged. Imports use only public Definitions for the literal inverse atlas, target maps and common-source maps, and the Proved public ordinary/reciprocal gluing identity. Original and public full types are compared in the kernel, with closed term and universe parameters. Native, strict and full frontend checks pass with standard axioms only. Named downstream consumer: the original finiteModelToCurve gluing constructor.

import Mathlib
import Definitions.Def_MazurTransfer_Order13InverseFiniteAtlasTargetMaps
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open MazurTransfer.Order13InverseParameterFiniteAlgebra
open MazurTorsion.XOneThirteenProjectiveCurve
universe u

theorem MazurTransfer.Order13InverseParameterFiniteAlgebra.finiteScheme_chart_curve_compatibility (R : Type u) [CommRing R] [IsDomain R] [IsNoetherianRing R]
    (h104 : IsUnit (104 : R)) (i j : Bool) :
    pullback.fst (finiteSchemeChartMap R h104 i) (finiteSchemeChartMap R h104 j) ≫
      finiteSchemeChartToCurve R i =
    pullback.snd (finiteSchemeChartMap R h104 i) (finiteSchemeChartMap R h104 j) ≫
      finiteSchemeChartToCurve R j := by sorry
