-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_fifthPowerRange_eq_sixteenthPowerKernel_of_card_eighty
-- name    : MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerRange_eq_sixteenthPowerKernel_of_card_eighty
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:12:42.274706+00:00
-- url     : https://prove2.me/theorems/3e5b843f-6483-4782-b478-74d3d757c693
-- title:
--   In a cyclic group of order $80$, fifth powers are the $16$-torsion kernel
-- statement:
--   Let $G$ be a finite cyclic commutative group with $|G|=80$. Let $[m]:G\to G$ denote the $m$th-power homomorphism $x\mapsto x^m$. Then $$\mathrm{im}[5]=\ker[16].$$ This supplies the membership test for fifth powers in the multiplicative group of a field with $81$ elements.
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

theorem MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerRange_eq_sixteenthPowerKernel_of_card_eighty
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (hcard : Nat.card G = 80) :
    (powMonoidHom 5 : G →* G).range =
      (powMonoidHom 16 : G →* G).ker := by sorry
