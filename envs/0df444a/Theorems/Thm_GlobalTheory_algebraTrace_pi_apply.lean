-- Prove2me | Theorems.Thm_GlobalTheory_algebraTrace_pi_apply
-- name    : GlobalTheory.algebraTrace_pi_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:05:34.95212+00:00
-- url     : https://prove2.me/theorems/7e4ed8be-2b63-4ca8-bd26-36e78d399233
-- title:
--   Global Theory: algebra Trace pi apply
-- statement:
--   The Global Theory construction uses the algebra Trace pi apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L19-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CovolumeBounds/NormDetMulProdSqLeOfEntryLe.lean#L19-L22

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
variable {E : Type*} [CommRing E] {ι : Type*} [Fintype ι]

theorem GlobalTheory.algebraTrace_pi_apply (x : ι → E) : Algebra.trace E (ι → E) x = ∑ i, x i := by sorry
