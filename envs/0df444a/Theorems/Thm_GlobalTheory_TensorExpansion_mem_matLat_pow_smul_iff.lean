-- Prove2me | Theorems.Thm_GlobalTheory_TensorExpansion_mem_matLat_pow_smul_iff
-- name    : GlobalTheory.TensorExpansion.mem_matLat_pow_smul_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-24T04:22:46.946801+00:00
-- url     : https://prove2.me/theorems/9de29ed2-a965-4089-a397-086ffb73401b
-- title:
--   Tensor Expansion: mem mat Lat pow smul iff
-- statement:
--   The Tensor Expansion construction uses the mem mat Lat pow smul iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumPureTensorOfIsTensorDepth.lean#L40-L43
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumPureTensorOfIsTensorDepth.lean#L40-L43

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

theorem GlobalTheory.TensorExpansion.mem_matLat_pow_smul_iff (ϖ : kˣ) (e : ℕ) {m n : ℕ} {Z : Matrix (Fin m) (Fin n) k} :
    Z ∈ matLat (Fin m) (ϖ ^ e • stdLat k (Fin n)) ↔ ∀ i j, (((ϖ ^ e)⁻¹ : kˣ) : k) * Z i j ∈ 𝒪[k] := by sorry
