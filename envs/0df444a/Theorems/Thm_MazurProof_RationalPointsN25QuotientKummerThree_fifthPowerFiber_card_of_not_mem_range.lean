-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_fifthPowerFiber_card_of_not_mem_range
-- name    : MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerFiber_card_of_not_mem_range
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:12:16.971204+00:00
-- url     : https://prove2.me/theorems/59403962-e482-4c1b-8128-43fb7736a7db
-- title:
--   A non-fifth-power has no fifth roots
-- statement:
--   Let $G$ be a finite commutative group and let $c\in G$. If $c$ is not in the image of the fifth-power homomorphism $u\mapsto u^5$, then $$|\{u\in G:u^5=c\}|=0.$$ This supplies the empty-fiber case in the Kummer point count.
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

theorem MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerFiber_card_of_not_mem_range
    {G : Type*} [CommGroup G] [Finite G] {c : G}
    (hc : c ∉ (powMonoidHom 5 : G →* G).range) :
    Nat.card {u : G // u ^ 5 = c} = 0 := by sorry
