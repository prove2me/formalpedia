-- Prove2me | Theorems.Thm_MeasLearner_right_unit
-- name    : MeasLearner.right_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:43:14.875032+00:00
-- url     : https://prove2.me/theorems/11f7c0c3-bc89-4b9d-9d61-2b5103553b5a
-- title:
--   Meas Learner: right unit
-- statement:
--   Right-unit law at the evaluation level: with a constant family `fun _ => L`, the
--   `concatLearner` collapses under any selector to plain `L.learner.learn S x`. Holds
--   definitionally (`rfl`).
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Monad.lean#L91-L97
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Monad.lean#L91-L97

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Monad
set_option autoImplicit true
@[expose] public section
public section
universe u

theorem MeasLearner.right_unit
    {X : Type u} [MeasurableSpace X]
    (L : MeasLearner X)
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun _ => L.learner) sel).learn S x =
    L.learner.learn S x := by sorry
