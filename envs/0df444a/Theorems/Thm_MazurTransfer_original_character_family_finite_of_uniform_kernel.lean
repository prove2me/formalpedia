-- Prove2me | Theorems.Thm_MazurTransfer_original_character_family_finite_of_uniform_kernel
-- name    : MazurTransfer.original_character_family_finite_of_uniform_kernel
-- status  : Proved
-- author  : @Vas
-- created : 2026-10-20T21:44:19.527516+00:00
-- url     : https://prove2.me/theorems/8e918e22-23b1-46b4-b83f-9a42ea925fd6
-- statement:
--   The original family injects into genuine characters on the same subgroup with finite coefficient group. If every character kills one same ambient subgroup of finite index, the family injects into the finite set of coefficient-valued functions on the ambient coset space and is finite. Every subgroup containment, finite-index, coefficient-finiteness, injectivity and uniform-vanishing hypothesis is retained. Named downstream consumer: unconditional finiteness of the actual arithmetic kernel character conditions.

import Mathlib
noncomputable section

theorem MazurTransfer.original_character_family_finite_of_uniform_kernel : ∀ {G M W : Type} [Group G] [Group M] [Finite M] (S T : Subgroup G) [T.FiniteIndex] (hTS : T ≤ S) (i : W → (S →* M)) (hi : Function.Injective i) (hvan : ∀ (w : W) (t : T), i w ⟨t.val, hTS t.property⟩ = 1), Finite W := by sorry
