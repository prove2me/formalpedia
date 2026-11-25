-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_oneIndex_of_oneClass_of_supportOne
-- name    : GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-25T10:39:06.554324+00:00
-- url     : https://prove2.me/theorems/8a02e2f1-d4e4-5944-b4aa-6c2b059b67ae
-- title:
--   Sym Chain: one Index of one Class of support One
-- statement:
--   The Sym Chain construction uses the one Index of one Class of support One property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/OneIndexOfOneClassOfSupportOne.lean#L26-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/OneIndexOfOneClassOfSupportOne.lean#L26-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_EntriesWellDefined
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_OneIndexOfOneClassOfSupportOne
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
open GlobalTheory GlobalTheory.SymChain

theorem GlobalTheory.SymChain.oneIndex_of_oneClass_of_supportOne :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k]
      [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t]
      [DecidableEq t], S.OneClass t ν → S.SupportOne t → S.OneIndex t ν := by sorry
