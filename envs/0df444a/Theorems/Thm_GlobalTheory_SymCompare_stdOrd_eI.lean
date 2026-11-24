-- Prove2me | Theorems.Thm_GlobalTheory_SymCompare_stdOrd_eI
-- name    : GlobalTheory.SymCompare.stdOrd_eI
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:18:00.397927+00:00
-- url     : https://prove2.me/theorems/d6243b80-6e66-436e-85a4-12d11caf7c59
-- title:
--   Sym Compare: std Ord e I
-- statement:
--   The Sym Compare construction uses the std Ord e I property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L229-L236
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/ExistsReindexIff.lean#L229-L236

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

theorem GlobalTheory.SymCompare.stdOrd_eI (κ : Type*) {t t' : Type*} (f : t ≃ t') {l : ℕ} (j c : ℕ) (h : j + c = l) :
    (eI (κ ⊕ Fin l) f j).trans (stdOrd κ t' j c h) = (stdOrd κ t j c h).trans (sE (eI (κ ⊕ Fin j) f j) c) := by sorry
