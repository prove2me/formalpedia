-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_reGL_conj
-- name    : GlobalTheory.SymCompare.reGL_conj
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:18:20.559854+00:00
-- url     : https://prove2.me/theorems/77a57a30-a68c-44b9-995f-7948c7484334
-- title:
--   Sym Compare: re GL conj
-- statement:
--   The Sym Compare construction uses the re GL conj property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L67-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L67-L73

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

theorem GlobalTheory.SymCompare.reGL_conj {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']
    (F : LatFrame k ι n) (F' : LatFrame k ι' m) (a : ι ≃ ι') (b : n ≃ m) (ho : a.trans F'.ord = F.ord.trans b)
    (hb : F'.bas = reGL b F.bas) (g : GL ι k) : F'.conj (reGL a g) = reGL b (F.conj g) := by sorry
