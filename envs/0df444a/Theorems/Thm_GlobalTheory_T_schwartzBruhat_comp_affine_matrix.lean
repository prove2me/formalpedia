-- Prove2me | Theorems.Thm_GlobalTheory_T_schwartzBruhat_comp_affine_matrix
-- name    : GlobalTheory.T.schwartzBruhat_comp_affine_matrix
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T22:44:45.909715+00:00
-- url     : https://prove2.me/theorems/8aa09635-6f35-4c2c-9319-4ed98e252503
-- title:
--   T: schwartz Bruhat comp affine matrix
-- statement:
--   The T construction uses the schwartz Bruhat comp affine matrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatCompAffineMatrixStatement.lean#L7-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SchwartzBruhatCompAffineMatrixStatement.lean#L7-L8

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrix
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ChLApply
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SchwartzBruhatCompAffineMatrixStatement
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

theorem GlobalTheory.T.schwartzBruhat_comp_affine_matrix : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R Q : Type) [Fintype R] [DecidableEq R] [Fintype Q] (A : GL R k) (a : Matrix R Q k) (Φ : Matrix R Q k → ℂ), Φ ∈ SB (Matrix R Q k) → (fun x => Φ (A.val * x + a)) ∈ SB (Matrix R Q k) := by sorry
