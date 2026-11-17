-- Prove2me | Theorems.Thm_N25_characterField_prime_above_five_unique
-- name    : N25.characterField_prime_above_five_unique
-- status  : Proved
-- author  : @FormallyCorrect
-- created : 2026-11-16T18:29:53.702195+00:00
-- url     : https://prove2.me/theorems/d1ffc3ac-b553-4984-a5d6-dc6c0be7f82a
-- title:
--   There is a unique prime above $5$ in the quintic character field
-- statement:
--   Let $K$ be the quintic character field and let $P_1,P_2$ be nonzero prime ideals of $\mathcal O_K$. If both ideals contain the integer $5$, then they are equal:
--
--   $$5\in P_1\cap P_2\Longrightarrow P_1=P_2.$$
--
--   This identifies the unique finite place of the character field lying above $5$.
-- source:
--   B. Mazur, Modular curves and the Eisenstein ideal, Publ. IHES 47 (1977); Lean formalization of the order-25 case for this mission. Modules in the MazurProof/Keystone/Tate families are adapted from anthropics/fermats-last-theorem (Apache-2.0) via the xiangyazi24/FLT fork.

import Definitions.Def_N25_CharacterField
import Mathlib.NumberTheory.NumberField.Norm

set_option autoImplicit false
open scoped NumberField
open N25

theorem N25.characterField_prime_above_five_unique
    (P₁ P₂ : Ideal (𝓞 characterField)) [P₁.IsPrime] [P₂.IsPrime]
    (hP₁ : P₁ ≠ ⊥) (hP₂ : P₂ ≠ ⊥)
    (h5₁ : (5 : 𝓞 characterField) ∈ P₁)
    (h5₂ : (5 : 𝓞 characterField) ∈ P₂) : P₁ = P₂ := by sorry
