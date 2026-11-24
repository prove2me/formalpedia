-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_Phi_reindex
-- name    : GlobalTheory.SymCompare.Phi_reindex
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T22:18:42.386632+00:00
-- url     : https://prove2.me/theorems/ede79af7-2721-4f4d-8492-1d975c9629ec
-- title:
--   Sym Compare: Phi reindex
-- statement:
--   The Sym Compare construction uses the Phi reindex property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L186-L196
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L186-L196

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
omit [Fintype n'] [DecidableEq n'] [Fintype m'] [DecidableEq m']

theorem GlobalTheory.SymCompare.Phi_reindex (P : TypeDatum k n) (e : n ≃ m) (f : n' ≃ m') (μ : kˣ →* ℂˣ) (x : Matrix (m ⊕ m') m k) :
    (P.reindex e).Phi m' μ x = P.Phi n' μ (x.submatrix (e.sumCongr f) e) := by sorry
