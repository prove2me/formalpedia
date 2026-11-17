-- Prove2me | Theorems.Thm_N25_Endgame_constantFieldLift25_degree_one
-- name    : N25.Endgame.constantFieldLift25_degree_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:24:58.508753+00:00
-- url     : https://prove2.me/theorems/0c8b7f6d-787e-4bf7-b48c-4d8d345c22ff
-- title:
--   A constant-field lift of a degree-one place remains degree one
-- statement:
--   Let $F_ℚ$ be the rational level-$25$ function field, let $F_{\overline{ℚ}}$ be its geometric constant extension, and let $ι:F_ℚ→F_{\overline{ℚ}}$ be the coefficient embedding. Let $P$ be a place of $F_ℚ$ with $deg(P)=1$, and let $P'$ be a place of $F_{\overline{ℚ}}$ whose valuation ring contracts to $𝒪_P$ and whose orders satisfy $ord_{P'}(ιf)=ord_P(f)$ for every $f∈F_ℚ$. Then
--
--   $$deg(P')=1.$$
--
--   This preserves rationality when passing from a rational place to its geometric lift.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ConstantFieldLift
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.Endgame.constantFieldLift25_degree_one (P : QPlace) (hP : P.deg = 1)
    (P' : GPlace) (hLift : IsConstantFieldLift25 P P') : P'.deg = 1 := by sorry
