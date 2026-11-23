-- Prove2me | Theorems.Thm_KernelRank_hasDerivAt_operatorOrbit
-- name    : KernelRank.hasDerivAt_operatorOrbit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:07:19.797027+00:00
-- url     : https://prove2.me/theorems/553a4299-357c-4a40-aa81-177b89c008b1
-- title:
--   Kernel Rank: has Deriv At operator Orbit
-- statement:
--   The Kernel Rank construction uses the has Deriv At operator Orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean#L38-L42
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean#L38-L42

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

theorem KernelRank.hasDerivAt_operatorOrbit (A : E →L[ℂ] E) (v : E)
    (β : E →L[ℂ] ℂ) (t : ℝ) :
    HasDerivAt (operatorOrbit A v β) (operatorOrbit A (A v) β t) t := by sorry
