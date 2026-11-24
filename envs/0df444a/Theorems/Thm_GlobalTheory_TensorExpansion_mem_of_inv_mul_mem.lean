-- Prove2me | Theorems.Thm_GlobalTheory_TensorExpansion_mem_of_inv_mul_mem
-- name    : GlobalTheory.TensorExpansion.mem_of_inv_mul_mem
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:03:21.615516+00:00
-- url     : https://prove2.me/theorems/3a82ab55-0573-41ab-8116-aaf56325fa80
-- title:
--   Tensor Expansion: mem of inv mul mem
-- statement:
--   The Tensor Expansion construction uses the mem of inv mul mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumPureTensorOfIsTensorDepth.lean#L33-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumPureTensorOfIsTensorDepth.lean#L33-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_HasCompactSupportFlatIntegrand
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsSumPureTensorOfIsTensorDepth
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory GlobalTheory.FunObj
noncomputable section
open GlobalTheory GlobalTheory.TensorExpansion
open GlobalTheory.SplitFlip ValuativeRel Matrix
open scoped Pointwise
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.TensorExpansion.mem_of_inv_mul_mem {ϖ : kˣ} (hϖ : IsUnif ϖ) (e : ℕ) {x : k}
    (h : (((ϖ ^ e)⁻¹ : kˣ) : k) * x ∈ 𝒪[k]) : x ∈ 𝒪[k] := by sorry
