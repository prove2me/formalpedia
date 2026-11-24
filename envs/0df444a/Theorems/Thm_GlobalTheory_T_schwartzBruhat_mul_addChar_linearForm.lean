-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartzBruhat_mul_addChar_linearForm
-- name    : GlobalTheory.T.schwartzBruhat_mul_addChar_linearForm
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T22:46:20.338823+00:00
-- url     : https://prove2.me/theorems/4c973153-bf8b-44ba-8618-d2dc82a3076e
-- title:
--   T: schwartz Bruhat mul add Char linear Form
-- statement:
--   The T construction uses the schwartz Bruhat mul add Char linear Form property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMulAddCharLinearFormStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatMulAddCharLinearFormStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMulAddCharLinearForm
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatMulAddCharLinearFormStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.schwartzBruhat_mul_addChar_linearForm : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → ∀ (R Q : Type) [Fintype R] [Fintype Q] (f : Matrix R Q k →ₗ[k] k) (z : k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => (ψ (f x + z) : ℂ) * Φ x) ∈ SB (Matrix R Q k) := by sorry
