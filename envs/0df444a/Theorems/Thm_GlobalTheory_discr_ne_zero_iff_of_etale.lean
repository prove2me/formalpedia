-- Prove2me | Theorems.Thm_GlobalTheory_discr_ne_zero_iff_of_etale
-- name    : GlobalTheory.discr_ne_zero_iff_of_etale
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:15:42.198556+00:00
-- url     : https://prove2.me/theorems/4d2cf2c8-a8d7-4485-ae88-5f33cf67f0aa
-- title:
--   Global Theory: discr ne zero iff of etale
-- statement:
--   The Global Theory construction uses the discr ne zero iff of etale property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L155-L163
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L155-L163

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_LinearIndependentRealOfIntOfDiscrete
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CovolumeBounds_NormDetMulProdSqLeOfEntryLe
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct Matrix
open Module Algebra
open GlobalTheory
variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]
variable {K A} {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.discr_ne_zero_iff_of_etale [Algebra.Etale K A] (h : Fintype.card ι = finrank K A)
    (v : ι → A) : discr K v ≠ 0 ↔ LinearIndependent K v := by sorry
