-- Prove2me | Theorems.Thm_GlobalTheory_LevZeroGen_upZero_mem_lev
-- name    : GlobalTheory.LevZeroGen.upZero_mem_lev
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:13:39.990038+00:00
-- url     : https://prove2.me/theorems/b04160ee-9e06-4a34-ae24-7a0d1090ab86
-- title:
--   Lev Zero Gen: up Zero mem lev
-- statement:
--   The Lev Zero Gen construction uses the up Zero mem lev property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/UpZeroMemLev.lean#L27-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/UpZeroMemLev.lean#L27-L39

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
noncomputable section
open GlobalTheory GlobalTheory.LevZeroGen
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
open ValuativeRel Matrix
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : _root_.GlobalTheory.SymChain.SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem GlobalTheory.LevZeroGen.upZero_mem_lev (x : GL (Fin κ ⊕ Fin (s + 1)) k) :
    _root_.GlobalTheory.LevZeroGen.upZero S t x ∈
        ((S.T t).lev 0 (s + 1)
          (Nat.zero_add _)).J ↔
      x ∈ S.P.J := by sorry
