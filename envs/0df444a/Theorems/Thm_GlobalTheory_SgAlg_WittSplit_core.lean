-- Prove2me | Theorems.Thm_GlobalTheory_SgAlg_WittSplit_core
-- name    : GlobalTheory.SgAlg.WittSplit.core
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T19:54:30.505433+00:00
-- url     : https://prove2.me/theorems/4af711ed-26b0-445c-bd24-e7c0fc7a4f92
-- title:
--   Witt Split: core
-- statement:
--   The Witt Split construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L118-L147
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/FlagMeasures/WittFreeTuplesSplitQuadraticEtale.lean#L118-L147

import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_InFrameStabilizer
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_FlagMeasures_WittFreeTuplesSplitQuadraticEtale
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.SgAlg Matrix Module
noncomputable section
open GlobalTheory GlobalTheory.SgAlg GlobalTheory.SgAlg.WittSplit
variable {F : Type} [Field F] {m k : Type} [Fintype m] [DecidableEq m] [Fintype k] [DecidableEq k]

theorem GlobalTheory.SgAlg.WittSplit.core (u u' : Matrix m k F) (φ φ' : Matrix k m F) (hu : ∃ L : Matrix k m F, L * u = 1)
    (hu' : ∃ L : Matrix k m F, L * u' = 1) (hφ : ∃ ψ : Matrix m k F, φ * ψ = 1)
    (hφ' : ∃ ψ : Matrix m k F, φ' * ψ = 1) (h : φ * u = φ' * u') :
    ∃ A : Matrix m m F, IsUnit A.det ∧ A * u = u' ∧ φ' * A = φ := by sorry
