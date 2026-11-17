-- Prove2me | Theorems.Thm_N25_Endgame_cusp_constant_fibre_degree25
-- name    : N25.Endgame.cusp_constant_fibre_degree25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:32.027317+00:00
-- url     : https://prove2.me/theorems/46c3de80-8cb4-41a8-ac87-80166bbdfabd
-- title:
--   The geometric fibre over a closed place has cardinality equal to its degree
-- statement:
--   Let $Q$ be a place of the rational level-$25$ function field and let $F_{\overline{\mathbb Q}}/F_{\mathbb Q}$ be the constant-field extension. The set of geometric places whose valuation rings contract to $\mathcal O_Q$ is finite, and
--
--   $$\bigl|\{P:\mathcal O_P\cap F_{\mathbb Q}=\mathcal O_Q\}\bigr|=\deg Q.$$
--
--   This converts the number of geometric lifts into the degree of the corresponding rational closed point.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_essFiniteType_of_transcendental_of_finiteDimensional
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Theorems.Thm_AlgebraicCurve_Place_sum_deg_fiberConstants_eq_deg_of_isCurveOver

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false
open AlgebraicCurve
open N25
open N25.Endgame

theorem N25.Endgame.cusp_constant_fibre_degree25 (Q : QPlace) :
    {P : GPlace | P.toValuationSubring.comap emb25.toRingHom = Q.toValuationSubring}.Finite ∧
    Nat.card {P : GPlace |
      P.toValuationSubring.comap emb25.toRingHom = Q.toValuationSubring} = Q.deg := by sorry
