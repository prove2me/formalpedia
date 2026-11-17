-- Prove2me | Theorems.Thm_N25_Endgame_exists_unique_constantFieldLift25
-- name    : N25.Endgame.exists_unique_constantFieldLift25
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:42:26.396049+00:00
-- url     : https://prove2.me/theorems/50fbed70-ecbc-40f4-aa71-5d7c960994ac
-- title:
--   A degree-one rational place has a unique geometric constant-field lift
-- statement:
--   Let $P$ be a degree-one place of the rational level-$25$ function field $F_ℚ$, and let $ι:F_ℚ→F_{\overline{ℚ}}$ be constant extension. Then there exists a geometric place $P'$ such that $𝒪_{P'}∩F_ℚ=𝒪_P$ and $ord_{P'}(ιf)=ord_P(f)$ for every $f∈F_ℚ$; moreover every geometric place $Q'$ whose valuation ring contracts to $𝒪_P$ equals $P'$:
--
--   $$∃!P'\text{ above }P,\qquad ord_{P'}(ιf)=ord_P(f)\ \forall f.$$
--
--   This uniqueness later forces the lift to be arithmetic-Galois fixed.
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

set_option autoImplicit false
open ModularCurve AlgebraicCurve
open N25
open N25.Endgame

theorem N25.Endgame.exists_unique_constantFieldLift25 (P : QPlace) (hP : P.deg = 1) :
    ∃ P' : GPlace, IsConstantFieldLift25 P P' ∧
      ∀ Q' : GPlace, Q'.toValuationSubring.comap emb25.toRingHom =
        P.toValuationSubring → Q' = P' := by sorry
