-- Prove2me | Theorems.Thm_KernelRank_differentialOperator_operatorOrbit
-- name    : KernelRank.differentialOperator_operatorOrbit
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-23T02:07:12.152869+00:00
-- url     : https://prove2.me/theorems/328bba62-e660-4b08-9797-cfea2be141c1
-- title:
--   Kernel Rank: differential Operator operator Orbit
-- statement:
--   The Kernel Rank construction uses the differential Operator operator Orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean#L59-L64
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean#L59-L64

import Definitions.Def_KernelRankLean_TranslationSemigroup
import Definitions.Def_KernelRankLean_Differential
set_option autoImplicit true
open Polynomial NNReal
open KernelRank
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
attribute [local instance] KernelRank._p2m_local_instance_4c459f894a_30
attribute [local instance] KernelRank._p2m_local_instance_4c459f894a_31
attribute [local instance] KernelRank._p2m_local_instance_4c459f894a_32

theorem KernelRank.differentialOperator_operatorOrbit (A : E →L[ℂ] E) (v : E)
    (β : E →L[ℂ] ℂ) (p : ℂ[X]) {t : ℝ} (ht : 0 ≤ t) :
    differentialOperator p (operatorOrbit A v β) t =
      operatorOrbit A (aeval A p v) β t := by sorry
