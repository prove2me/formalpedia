-- Prove2me | Theorems.Thm_GlobalTheory_SymLevelExists_map_symSumInt
-- name    : GlobalTheory.SymLevelExists.map_symSumInt
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T22:10:36.200865+00:00
-- url     : https://prove2.me/theorems/32b41582-d4d7-4a46-bfeb-7b9136368a85
-- title:
--   Sym Level Exists: map sym Sum Int
-- statement:
--   The Sym Level Exists construction uses the map sym Sum Int property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsSymmetricPositionLevel.lean#L100-L103
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/TwistedOperators/ExistsIsSymmetricPositionLevel.lean#L100-L103

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
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem GlobalTheory.SymLevelExists.map_symSumInt {F : Type} [Field F] (f : 𝒪[k] →+* F) {κ l : ℕ} (g : GL (Fin κ ⊕ Fin l) 𝒪[k]) :
    f (symSumInt g) = symSum (Matrix.GeneralLinearGroup.map f g) := by sorry
