-- Prove2me | Theorems.Thm_MeasLearner_left_unit
-- name    : MeasLearner.left_unit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:43:07.951179+00:00
-- url     : https://prove2.me/theorems/1a481e57-278a-480b-8898-ef95a6f1ccd0
-- title:
--   Meas Learner: left unit
-- statement:
--   Left-unit law at the evaluation level: with a constant selector `fun _ => n`, the
--   `concatLearner` of a family evaluates at `(S, x)` to `(family n).learner.learn S x`.
--   Holds definitionally (`rfl`): `concatLearner` with a constant selector reduces to
--   evaluating the selected family member.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Monad.lean#L80-L86
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Monad.lean#L80-L86

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Monad
set_option autoImplicit true
@[expose] public section
public section
universe u

theorem MeasLearner.left_unit
    {X : Type u} [MeasurableSpace X]
    (family : ℕ → MeasLearner X)
    [_hfam : UniformMeasurableBatchFamily (fun n => (family n).learner)]
    (n : ℕ) {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun i => (family i).learner) (fun _ => n)).learn S x =
    (family n).learner.learn S x := by sorry
