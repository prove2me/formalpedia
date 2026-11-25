-- Prove2me | Theorems.Thm_GlobalTheory_SymSupport_exists_int_inv
-- name    : GlobalTheory.SymSupport.exists_int_inv
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:56.018965+00:00
-- url     : https://prove2.me/theorems/f2b33b9f-f64c-4ab1-8fdd-3e5f4766c2e2
-- title:
--   Sym Support: exists int inv
-- statement:
--   The Sym Support construction uses the exists int inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L74-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainSupportOneOfPattern.lean#L74-L79

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainSupportOneOfPattern
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
noncomputable section
open GlobalTheory GlobalTheory.SymSupport
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SymSupport.exists_int_inv {U : Matrix n n k} (hU : IntM U) (hd : U.det = 1) : ∃ V, IntM V ∧ U * V = 1 := by sorry
