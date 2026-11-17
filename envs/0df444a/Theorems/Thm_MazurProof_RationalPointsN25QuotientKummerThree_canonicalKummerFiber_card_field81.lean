-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_canonicalKummerFiber_card_field81
-- name    : MazurProof.RationalPointsN25QuotientKummerThree.canonicalKummerFiber_card_field81
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:13:14.56906+00:00
-- url     : https://prove2.me/theorems/8042bbf6-abcb-44ea-8ace-9b486400e61d
-- title:
--   Every canonical Kummer fiber over $𝔽_{81}$ has its prescribed size
-- statement:
--   Let $K$ be a finite field with $|K|=81$ and decidable equality, and let $e,t\in K$. Let $F_e(r,t)$ be the canonical Kummer polynomial, and let $s_e(t)$ be the explicitly defined fiber-size function that treats a vanishing leading coefficient separately and otherwise applies the fifth-power criterion. Then $$|\{r\in K:F_e(r,t)=0\}|=s_e(t).$$ This reduces the quartic-extension point count to a finite sum of one-dimensional Kummer fibers.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Definitions.Def_N25_ExplicitWeilThreeDefs
import Definitions.Def_N25_ExplicitKummerThree

open MazurProof
open MazurProof.RationalPointsN25QuotientKummerThree
open MazurProof.RationalPointsN25QuotientF2
open scoped Pointwise

theorem MazurProof.RationalPointsN25QuotientKummerThree.canonicalKummerFiber_card_field81
    {K : Type*} [Field K] [Finite K] [DecidableEq K]
    (hcard : Nat.card K = 81) (e t : K) :
    Nat.card {r : K // canonicalKummerPolynomial25Three e r t = 0} =
      canonicalKummerFiberSizeField81 e t := by sorry
