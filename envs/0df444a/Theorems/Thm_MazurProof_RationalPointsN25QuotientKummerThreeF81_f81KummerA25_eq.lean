-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81KummerA25_eq
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerA25_eq
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:55.16778+00:00
-- url     : https://prove2.me/theorems/01b66087-eb14-4fcb-a741-f51fbb1c7407
-- title:
--   The first Segre--Kummer coefficient over $\mathbf F_{81}$
-- statement:
--   Let $e=1+2q+2q^2\in\mathbf F_{81}$ and define the structural Segre coefficient $A(e)=2e^3+e+1$. Let $A_{81}=2+2q^3$ be the stored explicit constant. Then
--
--   $$A(e)=A_{81}.$$
--
--   This connects the symbolic Segre cubic to its executable $\mathbf F_{81}$ coefficient table.
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

theorem MazurProof.RationalPointsN25QuotientKummerThreeF81.f81KummerA25_eq :
    segreCoefficientA25Three f81FifthRoot25 = f81KummerA25 := by sorry
