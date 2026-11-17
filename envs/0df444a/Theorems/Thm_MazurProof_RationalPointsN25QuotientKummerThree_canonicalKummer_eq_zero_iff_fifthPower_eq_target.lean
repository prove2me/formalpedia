-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_canonicalKummer_eq_zero_iff_fifthPower_eq_target
-- name    : MazurProof.RationalPointsN25QuotientKummerThree.canonicalKummer_eq_zero_iff_fifthPower_eq_target
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:12:58.623201+00:00
-- url     : https://prove2.me/theorems/dd77ebf4-a9cd-41e5-ace7-ad37b7b3fb0c
-- title:
--   The Kummer equation is a fifth-power equation off its denominator locus
-- statement:
--   Let $K$ be a field of characteristic $3$, and let $e,t,r\in K$. Write $D_e(t)$ for the canonical Kummer denominator, $F_e(r,t)$ for the canonical Kummer polynomial, and $T_e(t)$ for its normalized target. If $D_e(t)\ne0$, then $$F_e(r,t)=0\quad\Longleftrightarrow\quad r^5=T_e(t).$$ This converts each regular Kummer fiber into a standard fifth-power fiber.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_ExplicitKummerThree

open MazurProof
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientF2
variable {K : Type*} [Field K] [CharP K 3]
omit [CharP K 3]

theorem MazurProof.RationalPointsN25QuotientKummerThree.canonicalKummer_eq_zero_iff_fifthPower_eq_target
    (e t : K) {r : K}
    (hden : canonicalKummerDenominator25Three e t ≠ 0) :
    canonicalKummerPolynomial25Three e r t = 0 ↔
      r ^ 5 = canonicalKummerTarget25Three e t := by sorry
