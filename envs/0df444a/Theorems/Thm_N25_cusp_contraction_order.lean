-- Prove2me | Theorems.Thm_N25_cusp_contraction_order
-- name    : N25.cusp_contraction_order
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:56:07.474768+00:00
-- url     : https://prove2.me/theorems/05e454fd-5431-4705-8914-c604838eebc2
-- title:
--   Orders are preserved under contraction from the geometric field
-- statement:
--   Let $Q$ be a rational place and $P$ a geometric place such that the valuation ring of $Q$ is the contraction of the valuation ring of $P$ along the constant-field embedding $F_{\mathbb Q}\hookrightarrow F_{\overline{\mathbb Q}}$. Then every $f\in F_{\mathbb Q}$ satisfies
--
--   $$\operatorname{ord}_P(f)=\operatorname{ord}_Q(f),$$
--
--    where the occurrence of $f$ on the left denotes its geometric image. This preserves cusp widths and divisor orders under constant extension.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_N25_SelectedCusps
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_ramificationIndex_forgetConstants_eq_one_of_isConstantFieldExtension

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.cusp_contraction_order (Q : QPlace) (P : GPlace)
    (hQ : Q.toValuationSubring = P.toValuationSubring.comap emb25.toRingHom) (f : FQ) :
    P.ord (emb25 f) = Q.ord f := by sorry
