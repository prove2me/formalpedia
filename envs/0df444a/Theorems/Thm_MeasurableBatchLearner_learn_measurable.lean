-- Prove2me | Theorems.Thm_MeasurableBatchLearner_learn_measurable
-- name    : MeasurableBatchLearner.learn_measurable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T05:41:37.6248+00:00
-- url     : https://prove2.me/theorems/454eb5b3-cb31-4f88-8cf9-b89908ef1f80
-- title:
--   Measurable Batch Learner: learn measurable
-- statement:
--   Fixed-sample measurability: for fixed training data S,
--       L.learn S is a measurable function X → Bool.
--       This is the most commonly used consequence of MeasurableBatchLearner.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Properties.lean#L70-L75
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/FormalLearningTheory/Learner/Properties.lean#L70-L75

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Core
public import Mathlib.Algebra.Order.Module.Field
public import Mathlib.Data.EReal.Inv
public import Mathlib.Topology.Algebra.InfiniteSum.Order
public import Mathlib.Topology.MetricSpace.Bounded
public import Definitions.Def_LeanPool_FormalLearningTheory_Learner_Properties
set_option autoImplicit true
@[expose] public section
public section
universe u v

theorem MeasurableBatchLearner.learn_measurable
    {X : Type u} [MeasurableSpace X]
    (L : BatchLearner X Bool) [h : MeasurableBatchLearner X L]
    {m : ℕ} (S : Fin m → X × Bool) :
    Measurable (L.learn S) := by sorry
