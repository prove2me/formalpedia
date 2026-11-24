-- Prove2me | Theorems.Thm_GlobalTheory_TensorExpansion_exists_sum_pureTensor
-- name    : GlobalTheory.TensorExpansion.exists_sum_pureTensor
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T21:04:09.336874+00:00
-- url     : https://prove2.me/theorems/b3a25c36-90d7-431c-96c0-fb55ec337290
-- title:
--   Tensor Expansion: exists sum pure Tensor
-- statement:
--   The Tensor Expansion construction uses the exists sum pure Tensor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumPureTensorOfIsTensorDepth.lean#L64-L142
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsSumPureTensorOfIsTensorDepth.lean#L64-L142

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

theorem GlobalTheory.TensorExpansion.exists_sum_pureTensor : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (G : GlobalTheory.SplitFlip.Grid k) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ∀ (e : ℕ) (γ : List GlobalTheory.SplitFlip.Edge) (T : G.Args → ℂ), G.IsTensor ϖ e γ T → ∃ (n : ℕ) (x : Fin n → ℂ) (φ : Fin n → ∀ b : GlobalTheory.SplitFlip.Edge, Matrix (Fin (G.rank b.tgt)) (Fin (G.rank b.src)) k → ℂ), (∀ i, ∀ b ∈ γ, GlobalTheory.SplitFlip.IsNatDatum ϖ e (φ i b)) ∧ ∀ z, T z = ∑ i, x i * G.lines₂ γ (φ i) z := by sorry
