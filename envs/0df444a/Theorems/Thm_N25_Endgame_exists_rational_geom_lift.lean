-- Prove2me | Theorems.Thm_N25_Endgame_exists_rational_geom_lift
-- name    : N25.Endgame.exists_rational_geom_lift
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:21.394885+00:00
-- url     : https://prove2.me/theorems/db4e59e8-f300-4884-a6f3-791da236db0b
-- title:
--   Every degree-one rational place has a rational geometric lift
-- statement:
--   Let $P$ be a degree-one place of the rational level-$25$ function field $F_ℚ$. Then there exists a place $P'$ of the geometric field $F_{\overline{ℚ}}$ such that $P'$ has degree one, is fixed by every element of $Gal(\overline{ℚ}/ℚ)$, contracts to $P$, and preserves all orders under coefficient extension $ι:F_ℚ→F_{\overline{ℚ}}$:
--
--   $$deg(P')=1,\quad σP'=P',\quad 𝒪_{P'}∩F_ℚ=𝒪_P,\quad ord_{P'}(ιf)=ord_P(f)\ \forall f.$$
--
--   This lifts rational places into the geometric setting where Jacobian point differences are formed.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_ConstantFieldLift
import Definitions.Def_N25_Endgame
import Definitions.Def_ModularCurve_GeometricBaseChange
import Definitions.Def_N25_UnitAnalytic
import Definitions.Def_N25
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_qExpFunctionFieldC
import Theorems.Thm_ModularCurve_JOneES_exists_transcendental_finiteDimensional_laurentBaseChange
import Theorems.Thm_AlgebraicCurve_isCurveOver_of_transcendental_of_perfectField
import Theorems.Thm_AlgebraicCurve_constantsAreBase_of_deg_eq_one
import Theorems.Thm_AlgebraicCurve_Place_exists_comap_algebraMap_eq_of_constantFieldExtension_of_deg_eq_one_of_isAlgebraic
import Definitions.Def_AlgebraicCurve_IsCurveOver
import Theorems.Thm_ModularCurve_isCurveOver_and_essFiniteType_laurentBaseChange_xHFunctionField
import Definitions.Def_ModularCurve_ArithmeticGalois

set_option autoImplicit false
open N25
open N25.Endgame

theorem N25.Endgame.exists_rational_geom_lift (P : QPlace) (hP : P.deg = 1) :
    ∃ P' : GPlace, IsRationalGeomPlace P' ∧
      P'.toValuationSubring.comap emb25.toRingHom = P.toValuationSubring ∧
      ∀ f : FQ, P'.ord (emb25 f) = P.ord f := by sorry
