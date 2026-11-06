-- Prove2me | Theorems.Thm_OAI_SevenEighths_InverseMoment_column_fiber_sieve
-- name    : OAI.SevenEighths.InverseMoment.column_fiber_sieve
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-05T23:00:36.263026+00:00
-- url     : https://prove2.me/theorems/e5d3e35f-d4a9-41d5-b83a-97eec2bf732a
-- title:
--   Inverse Moment: column fiber sieve
-- statement:
--   The Inverse Moment construction uses the column fiber sieve property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SieveComposition.lean#L56-L93
-- source:
--   https://github.com/LW56e2/quasi-riemann-improved/blob/b83dbbd914c5751acf9bc3389cde58970437278f/lean/OAI/NumberTheory/DirichletL/Descent/SieveComposition.lean#L56-L93

import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_Fibers
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Definitions.Def_OAI_NumberTheory_DirichletL_Descent_SieveComposition
set_option autoImplicit false
open OAI
open OAI.SevenEighths OAI.SevenEighths.InverseMoment
open scoped BigOperators
noncomputable section

theorem OAI.SevenEighths.InverseMoment.column_fiber_sieve {K X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (rows : Finset K) (source : Finset X) (target : Finset Y)
    (φ : X → Y) (q : K → Y → ℂ) (a : X → ℂ) (Q D : ℝ) (hQ : 0 ≤ Q)
    (hφ : ∀ x ∈ source, φ x ∈ target)
    (hfiber : ∀ y ∈ target, ((source.filter (fun x => φ x = y)).card : ℝ) ≤ D)
    (hsieve : ∀ f : Y → ℂ,
      (∑ k ∈ rows, ‖∑ y ∈ target, q k y * f y‖ ^ 2) ≤
        Q * ∑ y ∈ target, ‖f y‖ ^ 2) :
    (∑ k ∈ rows, ‖∑ x ∈ source, q k (φ x) * a x‖ ^ 2) ≤
      Q * D * ∑ x ∈ source, ‖a x‖ ^ 2 := by sorry
