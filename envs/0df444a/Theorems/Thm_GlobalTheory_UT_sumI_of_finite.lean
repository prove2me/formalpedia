-- Prove2me | Theorems.Thm_GlobalTheory_UT_sumI_of_finite
-- name    : GlobalTheory.UT.sumI_of_finite
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T12:43:41.171632+00:00
-- url     : https://prove2.me/theorems/21ce3f06-179b-48f1-92bf-a615cafe2c2b
-- title:
--   UT: sum I of finite
-- statement:
--   The UT construction uses the sum I of finite property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SumIOfFinite.lean#L6-L14
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/UniformizationProofs/SumIOfFinite.lean#L6-L14

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Uniformization_TXFrame
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_UniformizationProofs_SumIOfFinite
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.UT

theorem GlobalTheory.UT.sumI_of_finite {R : Type} [CommRing R] (I : Ideal R) {E Ix : Type} [AddCommGroup E] [Module R E] (x : Ix → E)
    (S : Finset Ix) (hS : ∀ i, i ∉ S → x i = 0) : SumI I x (∑ i ∈ S, x i) := by sorry
