-- Prove2me | Theorems.Thm_KernelRank_iteratedDerivWithin_operatorOrbit
-- name    : KernelRank.iteratedDerivWithin_operatorOrbit
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-23T02:07:25.263921+00:00
-- url     : https://prove2.me/theorems/4ec3745c-dec4-4d0d-a4e3-4cb1540f9ffe
-- title:
--   Kernel Rank: iterated Deriv Within operator Orbit
-- statement:
--   The Kernel Rank construction uses the iterated Deriv Within operator Orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean#L44-L57
-- source:
--   https://github.com/OlliNiemitalo/kernel-rank-lean/blob/a406bf6714fea09066eb0ef896d01df205145675/KernelRankLean/Differential.lean#L44-L57

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

theorem KernelRank.iteratedDerivWithin_operatorOrbit (A : E →L[ℂ] E) (v : E)
    (β : E →L[ℂ] ℂ) (k : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    iteratedDerivWithin k (operatorOrbit A v β) (Set.Ici 0) t =
      operatorOrbit A ((A ^ k) v) β t := by sorry
