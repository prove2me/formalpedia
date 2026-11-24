-- Prove2me | Theorems.Thm_GlobalTheory_TensorExpansion_unitsPowInv_val
-- name    : GlobalTheory.TensorExpansion.unitsPowInv_val
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:29.384959+00:00
-- url     : https://prove2.me/theorems/1abd6394-ac5a-401c-b639-54d882661474
-- title:
--   Tensor Expansion: units Pow Inv val
-- statement:
--   The Tensor Expansion construction uses the units Pow Inv val property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumPureTensorOfIsTensorDepth.lean#L12-L13
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumPureTensorOfIsTensorDepth.lean#L12-L13

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

theorem GlobalTheory.TensorExpansion.unitsPowInv_val (ϖ : kˣ) (e : ℕ) : (((ϖ ^ e)⁻¹ : kˣ) : k) = ((ϖ : k) ^ e)⁻¹ := by sorry
