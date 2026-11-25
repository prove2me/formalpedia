-- Prove2me | Theorems.Thm_GlobalTheory_SymLevelExists_exists_isSymLevel
-- name    : GlobalTheory.SymLevelExists.exists_isSymLevel
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T22:10:22.833515+00:00
-- url     : https://prove2.me/theorems/510a5038-586d-49ea-9654-611d96b8074a
-- title:
--   Sym Level Exists: exists is Sym Level
-- statement:
--   The Sym Level Exists construction uses the exists is Sym Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsSymmetricPositionLevel.lean#L107-L122
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsSymmetricPositionLevel.lean#L107-L122

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_BlockTheory_TwistedDiscreteSeries_FramePositiveSum
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_UnipotentRadicalBasic
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_TwistedOperators_ExistsIsSymmetricPositionLevel
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix Topology GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
noncomputable section
open GlobalTheory GlobalTheory.SymLevelExists

theorem GlobalTheory.SymLevelExists.exists_isSymLevel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), HasConductor ψ 1 → ∀ ϖ : kˣ, IsUnif ϖ → ∀ ρ κ l : ℕ, ∃ P : TypeDatum k (Fin κ ⊕ Fin l), IsSymLevel ψ ϖ ρ P := by sorry
