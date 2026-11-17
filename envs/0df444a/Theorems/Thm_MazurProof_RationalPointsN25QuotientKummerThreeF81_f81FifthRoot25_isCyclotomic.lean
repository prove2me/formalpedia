-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThreeF81_f81FifthRoot25_isCyclotomic
-- name    : MazurProof.RationalPointsN25QuotientKummerThreeF81.f81FifthRoot25_isCyclotomic
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:14:32.680852+00:00
-- url     : https://prove2.me/theorems/d5b23721-d752-4916-aa40-f8e31a875a49
-- title:
--   The chosen element of $\mathbf F_{81}$ satisfies the fifth-cyclotomic equation
-- statement:
--   Let $\mathbf F_{81}=\mathbf F_3[q]/(q^4+2q^3+2)$ and let $e=1+2q+2q^2$. Then $e$ lies on the fifth-cyclotomic locus:
--
--   $$e^4+e^3+e^2+e+1=0.$$
--
--   This is the eigenvalue condition needed to diagonalize the order-five automorphism in the Kummer model.
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

theorem MazurProof.RationalPointsN25QuotientKummerThreeF81.f81FifthRoot25_isCyclotomic :
    IsCyclotomicFive25Three f81FifthRoot25 := by sorry
