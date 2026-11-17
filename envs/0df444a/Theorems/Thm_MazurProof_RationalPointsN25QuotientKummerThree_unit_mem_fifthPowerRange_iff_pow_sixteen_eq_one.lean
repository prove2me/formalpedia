-- Prove2me | Theorems.Thm_MazurProof_RationalPointsN25QuotientKummerThree_unit_mem_fifthPowerRange_iff_pow_sixteen_eq_one
-- name    : MazurProof.RationalPointsN25QuotientKummerThree.unit_mem_fifthPowerRange_iff_pow_sixteen_eq_one
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:12:18.490978+00:00
-- url     : https://prove2.me/theorems/a78a324d-0043-44ea-9234-b609a688b03f
-- title:
--   Fifth powers in $𝔽_{81}^×$ are detected by the $16$th power
-- statement:
--   Let $K$ be a finite field with $|K|=81$, and let $c\in K^×$. Then $c$ is a fifth power in $K^×$ exactly when its sixteenth power is one: $$c\in (K^×)^5\quad\Longleftrightarrow\quad c^{16}=1.$$ This is the executable fifth-power criterion for the characteristic-three quartic field.
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

theorem MazurProof.RationalPointsN25QuotientKummerThree.unit_mem_fifthPowerRange_iff_pow_sixteen_eq_one
    {K : Type*} [Field K] [Finite K]
    (hcard : Nat.card K = 81) {c : K} (hc : c ≠ 0) :
    Units.mk0 c hc ∈ (powMonoidHom 5 : Kˣ →* Kˣ).range ↔
      c ^ 16 = 1 := by sorry
