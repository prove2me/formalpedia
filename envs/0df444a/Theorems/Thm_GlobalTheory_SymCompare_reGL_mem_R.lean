-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_reGL_mem_R
-- name    : GlobalTheory.SymCompare.reGL_mem_R
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T12:25:58.057411+00:00
-- url     : https://prove2.me/theorems/6835749c-f836-4999-9821-791f8910bfb0
-- title:
--   Sym Compare: re GL mem R
-- statement:
--   The Sym Compare construction uses the re GL mem R property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L41-L47

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
variable {k : Type*} [Field k] {n m n' m' : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m'] {c : ℕ}

theorem GlobalTheory.SymCompare.reGL_mem_R (e : n ≃ m) {p : ℕ} {g : GL (n ⊕ Fin c) k} (hg : g ∈ R k n c p) :
    reGL (sE e c) g ∈ R k m c p := by sorry
