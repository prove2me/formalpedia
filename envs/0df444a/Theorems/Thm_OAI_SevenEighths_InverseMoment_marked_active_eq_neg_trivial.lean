-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_marked_active_eq_neg_trivial
-- name    : OAI.SevenEighths.InverseMoment.marked_active_eq_neg_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:00:07.054053+00:00
-- url     : https://prove2.me/theorems/9cbe82cc-08c2-4474-a665-8b034a5e5123
-- title:
--   Inverse Moment: marked active eq neg trivial
-- statement:
--   The Inverse Moment construction uses the marked active eq neg trivial property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean#L44-L54
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/LocalReflection.lean#L44-L54

import Mathlib.NumberTheory.GaussSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.Ring
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_LocalReflection
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] [Fintype F]

theorem OAI.SevenEighths.InverseMoment.marked_active_eq_neg_trivial (χ : MulChar F ℂ)
    (ψ : AddChar F ℂ) (hψ : ψ.IsPrimitive) (σ ε : Fˣ) (x : F) :
    localReflectionActive zeroMark χ ψ σ ε x =
      -localReflectionActive (fun t => (1 : MulChar F ℂ) t) χ ψ σ ε x := by sorry
