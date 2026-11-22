-- Prove2me | Theorems.Thm_MeasLearner_assoc
-- name    : MeasLearner.assoc
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:43:18.759665+00:00
-- url     : https://prove2.me/theorems/96a268c4-1c6c-4555-a1e4-d378d71a40c8
-- title:
--   Meas Learner: assoc
-- statement:
--   Associativity at the evaluation level: the `concatLearner` evaluation
--   `(concatLearner (fun n => (family n).learner) sel).learn S x` reduces definitionally
--   to `(family (sel S)).learner.learn S x`. Held by `rfl`; the identity is what lets
--   nested `concatLearner` selections compose into a single selector in downstream
--   constructions.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Monad.lean#L104-L111
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Monad.lean#L104-L111

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Closure
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Monad
set_option autoImplicit true
@[expose] public section
public section
universe u

theorem MeasLearner.assoc
    {X : Type u} [MeasurableSpace X]
    (family : ℕ → MeasLearner X)
    [_hfam : UniformMeasurableBatchFamily (fun n => (family n).learner)]
    (sel : {m : ℕ} → (Fin m → X × Bool) → ℕ)
    {m : ℕ} (S : Fin m → X × Bool) (x : X) :
    (concatLearner (fun n => (family n).learner) sel).learn S x =
    (family (sel S)).learner.learn S x := by sorry
