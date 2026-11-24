-- Prove2me | Theorems.Thm_GlobalTheory_T_exists_adapted_exponent_schwartzBruhat_lastColumn
-- name    : GlobalTheory.T.exists_adapted_exponent_schwartzBruhat_lastColumn
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T22:19:41.242844+00:00
-- url     : https://prove2.me/theorems/5349f1e2-1775-48da-a5a8-41b7403c1c80
-- title:
--   T: exists adapted exponent schwartz Bruhat last Column
-- statement:
--   The T construction uses the exists adapted exponent schwartz Bruhat last Column property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsAdaptedExponentSchwartzBruhatLastColumnStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsAdaptedExponentSchwartzBruhatLastColumnStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsAdaptedExponentSchwartzBruhatLastColumn
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsAdaptedExponentSchwartzBruhatLastColumnStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.exists_adapted_exponent_schwartzBruhat_lastColumn : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (n' : Type) [Fintype n'] [DecidableEq n'] (S : Set (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k → ℂ)), S.Finite → (∀ Ψ ∈ S, Ψ ∈ SB (Matrix (n ⊕ Fin 0) (n' ⊕ Fin (0 + 1)) k)) → ∀ ϖ : kˣ, IsUnif ϖ → ∃ e : ℕ, 1 ≤ e ∧ ∀ Ψ ∈ S, ∀ (x₀ : Matrix n n' k) (y : n → k), (Ψ (withCol x₀ y) ≠ 0 → y ∈ box n (ϖ ^ e)⁻¹) ∧ ∀ z ∈ box n (ϖ ^ e), Ψ (withCol x₀ (y + z)) = Ψ (withCol x₀ y) := by sorry
