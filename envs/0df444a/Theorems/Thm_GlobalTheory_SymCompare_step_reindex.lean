-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_step_reindex
-- name    : GlobalTheory.SymCompare.step_reindex
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-24T22:17:47.135804+00:00
-- url     : https://prove2.me/theorems/35c13e4b-a7d7-4cc1-802f-86c474de22b4
-- title:
--   Sym Compare: step reindex
-- statement:
--   The Sym Compare construction uses the step reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L170-L183
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L170-L183

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

theorem GlobalTheory.SymCompare.step_reindex (P : TypeDatum k n) (e : n ≃ m) (f : n' ≃ m') (μ : kˣ →* ℂˣ) (hμ : IsTame μ) :
    (P.reindex e).step m' μ hμ = (P.step n' μ hμ).reindex (e.sumCongr f) := by sorry
