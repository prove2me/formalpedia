-- Prove2me | Theorems.Thm_GlobalTheory_RootEx_RowSupport_row_support_uniform
-- name    : GlobalTheory.RootEx.RowSupport.row_support_uniform
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:28:36.414192+00:00
-- url     : https://prove2.me/theorems/feadf82d-34b4-462a-8a3c-c99dcb268f55
-- title:
--   Row Support: row support uniform
-- statement:
--   The Row Support construction uses the row support uniform property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RowSupportUniform.lean#L55-L92
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/RowSupportUniform.lean#L55-L92

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SimpleSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RootExchangeSupportAndFourierRelation
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_RowSupportUniform
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx
open Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.RootEx GlobalTheory.RootEx.RowSupport
open GlobalTheory.RootEx.ExchangeSupport

theorem GlobalTheory.RootEx.RowSupport.row_support_uniform : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c p : ℕ) (_ : 1 ≤ p) (_ : p < c) (ψ : AddChar k Circle) (_ : ψ ≠ 1) (A : Type) [AddCommGroup A] [Module ℂ A] (σ : Representation ℂ (GL (n ⊕ Fin c) k) A) (_ : IsSmoothRep σ) (F : A) (Ω : Set (GL (n ⊕ Fin c) k)) (_ : IsCompact Ω), ∃ B : Set (n → k), IsCompact B ∧ ∀ l : A →ₗ[ℂ] ℂ, IsNEquiv ψ p σ l → ∀ w ∈ Ω, ∀ u, u ∉ B → l (σ (rowE c p u) (σ w F)) = 0 := by sorry
