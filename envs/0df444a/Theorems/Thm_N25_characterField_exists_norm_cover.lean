-- Prove2me | Theorems.Thm_N25_characterField_exists_norm_cover
-- name    : N25.characterField_exists_norm_cover
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:41:59.82998+00:00
-- url     : https://prove2.me/theorems/fe98a548-caef-482e-919c-9194796b11f1
-- title:
--   At most seven ideals cover all norms up to $24$
-- statement:
--   Let $K=\mathbb Q(\zeta_{25})^{H_{25}}$ be the quintic character field, let $\mathcal O_K$ be its ring of integers, and let $N(I)$ denote the absolute norm of a nonzero integral ideal $I$. There is a finite set $S$ of nonzero ideals with at most seven elements that contains every nonzero ideal of norm at most $24$:
--
--   $$|S|\le 7\quad\text{and}\quad N(I)\le 24\Longrightarrow I\in S.$$
--
--   This supplies the finite norm cover used to bound the class number of the character field.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Mathlib
import Definitions.Def_N25_CharacterField
import Mathlib.NumberTheory.NumberField.Norm
import Definitions.Def_N25
import Mathlib.NumberTheory.RamificationInertia.Galois
import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Invariant.Basic

set_option autoImplicit false
open scoped NumberField nonZeroDivisors
open N25

theorem N25.characterField_exists_norm_cover :
    ∃ s : Finset (Ideal (𝓞 characterField))⁰, s.card ≤ 7 ∧
      ∀ I : (Ideal (𝓞 characterField))⁰,
        Ideal.absNorm (I : Ideal (𝓞 characterField)) ≤ 24 → I ∈ s := by sorry
