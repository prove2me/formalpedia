-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81KummerTarget25_eq
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerTarget25_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:13.65337+00:00
-- url     : https://prove2.me/theorems/6a392dc1-34e0-4e7a-8f95-9c2a12b60e15
-- title:
--   The executable Kummer target has the canonical formula
-- statement:
--   Let $e\in\mathbf F_{81}$ be the chosen fifth-cyclotomic element, and define $D_e(t)=1+A(e)t$ and $N_e(t)=t^2(B(e)+e^2t)$. Using the field inverse, including the convention $0^{-1}=0$, the executable target agrees with the canonical target for every $t\in\mathbf F_{81}$:
--
--   $$-N_e(t)\,D_e(t)^{-1}=T_e(t).$$
--
--   This connects the table computation to the target whose fifth roots form the Kummer fiber.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_ExplicitF81Field
import Definitions.Def_N25_ExplicitKummerThree
import Definitions.Def_N25_ExplicitKummerThreeF81

open MazurProof
open MazurProof.RationalPointsN25QuotientKummerThreeF81
open MazurProof.RationalPointsN25QuotientWeilThree
open MazurProof.RationalPointsN25QuotientKummerThree
open scoped BigOperators
attribute [local instance] Fintype.decidableForallFintype
  Fintype.decidableExistsFintype

theorem MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerTarget25_eq (t : F81) :
    f81Operations.mul
        (f81Operations.neg
          (canonicalKummerNumerator25Three f81FifthRoot25 t))
        (f81Inv (canonicalKummerDenominator25Three f81FifthRoot25 t)) =
      canonicalKummerTarget25Three f81FifthRoot25 t := by sorry
