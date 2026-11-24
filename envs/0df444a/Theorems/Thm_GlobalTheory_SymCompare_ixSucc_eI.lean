-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_ixSucc_eI
-- name    : GlobalTheory.SymCompare.ixSucc_eI
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T22:18:34.89388+00:00
-- url     : https://prove2.me/theorems/8ce500d9-e055-46e6-973b-3ada55610cb2
-- title:
--   Sym Compare: ix Succ e I
-- statement:
--   The Sym Compare construction uses the ix Succ e I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L207-L210
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L207-L210

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
variable {r t t' : Type*} [Fintype r] [DecidableEq r] [Fintype t] [DecidableEq t] [Fintype t'] [DecidableEq t']

theorem GlobalTheory.SymCompare.ixSucc_eI (r : Type*) {t t' : Type*} (f : t ≃ t') (j : ℕ) :
    ((eI r f j).sumCongr f).trans (ixSucc r t' j) = (ixSucc r t j).trans (eI r f (j + 1)) := by sorry
