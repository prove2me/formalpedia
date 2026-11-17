-- Prove2me | Theorems.Thm_N25_U25_rational_support_of_geometric_support
-- name    : N25.U25_rational_support_of_geometric_support
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:55:58.51745+00:00
-- url     : https://prove2.me/theorems/100684d1-030e-44ce-9a09-5222d4372bd6
-- title:
--   Geometric cuspidal support descends to rational support
-- statement:
--   Fix $U_i$ and assume its geometric image has order zero away from $P_0^G,…,P_4^G$. Then $$∀P, P≠P_0^ℚ∧⋯∧P≠P_4^ℚ⇒ord_P(U_i)=0.$$ This descends the support calculation to rational places.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_Units
import Definitions.Def_N25_SelectedCusps
import Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Definitions.Def_N25_Endgame
import Definitions.Def_AlgebraicCurve_ConstantFieldPullback
import Definitions.Def_FieldTheory_RatAlgClosureGalois
import Definitions.Def_ModularCurve_GeometricBaseChange
import Theorems.Thm_ModularCurve_ord_qInftyPlaceBar
import Theorems.Thm_AlgebraicCurve_Place_ord_eq_zero_of_isAlgebraic
import Theorems.Thm_AlgebraicCurve_Place_exists_forgetConstants_restrict_eq_of_isConstantFieldExtension

set_option autoImplicit false
open ModularCurve AlgebraicCurve N25.Endgame
open N25

theorem N25.U25_rational_support_of_geometric_support (i : Fin 5)
    (hG : ∀ W : GPlace, (∀ j : Fin 5, W ≠ pG25 j) →
      W.ord (emb25 (U25 i)) = 0) :
    ∀ P : QPlace, (∀ j : Fin 5, P ≠ pQ25 j) → P.ord (U25 i) = 0 := by sorry
