-- Prove2me | Theorems.Thm_GlobalTheory_T_isCompletelyReducible_kronecker_of_span_eq_top
-- name    : GlobalTheory.T.isCompletelyReducible_kronecker_of_span_eq_top
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T20:49:14.765294+00:00
-- url     : https://prove2.me/theorems/34d0131f-ef36-4527-870c-441ea843d4e1
-- title:
--   T: is Completely Reducible kronecker of span eq top
-- statement:
--   The T construction uses the is Completely Reducible kronecker of span eq top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsCompletelyReducibleKroneckerOfSpanEqTopStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/AdelicLatticeProofs/IsCompletelyReducibleKroneckerOfSpanEqTopStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsCompletelyReducibleKroneckerOfSpanEqTop
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_AdelicHermitianForms_AdelicPair
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_AdelicLatticeProofs_IsCompletelyReducibleKroneckerOfSpanEqTopStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.isCompletelyReducible_kronecker_of_span_eq_top : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (κ : Type) [Fintype κ] [DecidableEq κ] (G : Type) [Group G] (ρ : G →* Matrix ι ι ℂ) (ρ' : G →* Matrix κ κ ℂ), Submodule.span ℂ (Set.range ρ) = ⊤ → Submodule.span ℂ (Set.range ρ') = ⊤ → SS (Set.range fun g => ρ g ⊗ₖ ρ' g) := by sorry
