-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_om_submatrix
-- name    : GlobalTheory.SymCompare.om_submatrix
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-25T12:26:22.059405+00:00
-- url     : https://prove2.me/theorems/fd8d48a5-dbcb-4b4e-8646-45cb6be5d86c
-- title:
--   Sym Compare: om submatrix
-- statement:
--   The Sym Compare construction uses the om submatrix property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L96-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L96-L103

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_SiegelEisenstein_SymmetricPatternGroup
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_ExistsReindexIff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.SymCompare
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}

theorem GlobalTheory.SymCompare.om_submatrix (μ : kˣ →* ℂˣ) (E : n ≃ m) (E' : n' ≃ m') (h : GL n k) (Φ : Matrix n n' k → ℂ) :
    om μ 1 (reGL E h) (fun x => Φ (x.submatrix E E')) = fun x => om μ 1 h Φ (x.submatrix E E') := by sorry
