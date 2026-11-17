-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_fifthPowerFiber_card_of_mem_range
-- name    : MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerFiber_card_of_mem_range
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:12:43.431376+00:00
-- url     : https://prove2.me/theorems/14cd1454-8b51-45ce-8514-136fa8883e2a
-- title:
--   A fifth power in a cyclic group of order $80$ has five fifth roots
-- statement:
--   Let $G$ be a finite cyclic commutative group with $|G|=80$, and let $c\in G$ lie in the image of $x\mapsto x^5$. Then the fifth-power fiber over $c$ has cardinality five: $$|\{u\in G:u^5=c\}|=5.$$ This gives the nonempty fiber size used in the finite-field Kummer count.
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

theorem MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerFiber_card_of_mem_range
    {G : Type*} [CommGroup G] [Finite G] [IsCyclic G]
    (hcard : Nat.card G = 80) {c : G}
    (hc : c ∈ (powMonoidHom 5 : G →* G).range) :
    Nat.card {u : G // u ^ 5 = c} = 5 := by sorry
