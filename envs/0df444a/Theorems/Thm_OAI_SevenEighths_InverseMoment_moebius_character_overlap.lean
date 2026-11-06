-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_moebius_character_overlap
-- name    : OAI.SevenEighths.InverseMoment.moebius_character_overlap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T22:41:58.69956+00:00
-- url     : https://prove2.me/theorems/1c0252fc-0622-4f51-acfe-0227d1ccff66
-- title:
--   Inverse Moment: moebius character overlap
-- statement:
--   The Inverse Moment construction uses the moebius character overlap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Overlap.lean#L25-L33
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/Overlap.lean#L25-L33

import Mathlib.RingTheory.UniqueFactorizationDomain.Moebius
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Overlap
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open UniqueFactorizationMonoid
variable {M : Type*} [CommMonoidWithZero M] [UniqueFactorizationMonoid M]

theorem OAI.SevenEighths.InverseMoment.moebius_character_overlap (ψ : M →* ℂ) {j n₀ P₀ : M}
    (hjn : IsRelPrime j n₀) (hnP : IsRelPrime n₀ P₀) (hP : Squarefree P₀) :
    (moebius (j * n₀) : ℂ) * ψ (j * n₀) * ψ (j * P₀) =
      (moebius j : ℂ) * (moebius P₀ : ℂ) * (moebius (n₀ * P₀) : ℂ) *
        ψ j ^ 2 * ψ (n₀ * P₀) := by sorry
