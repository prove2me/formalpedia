-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_fifthPowerFiber_card_field81
-- name    : MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerFiber_card_field81
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:12:29.593426+00:00
-- url     : https://prove2.me/theorems/e2d63a44-4fb4-46f4-903e-627d7d3a8a66
-- title:
--   Fifth-power fibers over a field of size $81$ have sizes $1$, $5$, or $0$
-- statement:
--   Let $K$ be a finite field with $|K|=81$ and decidable equality, and let $c\in K$. Then $$|\{r\in K:r^5=c\}|=\begin{cases}1,&c=0,\5,&c\ne0\text{ and }c^{16}=1,\0,&c\ne0\text{ and }c^{16}\ne1.\end{cases}$$ This gives the complete one-variable fiber count needed for the Kummer model. Formalization note: decidable equality is required only to evaluate the displayed cases.
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

theorem MazurProof.RationalPointsN25QuotientKummerThree.fifthPowerFiber_card_field81
    {K : Type*} [Field K] [Finite K] [DecidableEq K]
    (hcard : Nat.card K = 81) (c : K) :
    Nat.card {r : K // r ^ 5 = c} =
      if c = 0 then 1 else if c ^ 16 = 1 then 5 else 0 := by sorry
