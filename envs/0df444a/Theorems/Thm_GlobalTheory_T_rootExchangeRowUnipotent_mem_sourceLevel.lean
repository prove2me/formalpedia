-- Prove2me | Theorems.Thm_GlobalTheory_T_rootExchangeRowUnipotent_mem_sourceLevel
-- name    : GlobalTheory.T.rootExchangeRowUnipotent_mem_sourceLevel
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T11:17:05.370796+00:00
-- url     : https://prove2.me/theorems/3a38234e-ec71-4afd-807d-9386f5b4c985
-- title:
--   T: root Exchange Row Unipotent mem source Level
-- statement:
--   The T construction uses the root Exchange Row Unipotent mem source Level property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeRowUnipotentMemSourceLevelStatement.lean#L8-L9
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/RootExchangeRowUnipotentMemSourceLevelStatement.lean#L8-L9

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentMemSourceLevel
import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_ContrFactor
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_RootExchangeRowUnipotentMemSourceLevelStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.rootExchangeRowUnipotent_mem_sourceLevel : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → ∀ j c (H : j + 1 + c = s) (r : ℕ), c = 2 * r → ∀ u : XIx (Fin κ) t j → k, u ∈ box (XIx (Fin κ) t j) (S.ϖ ^ (r + 1)) → rowE (c + 1 + 1) (r + 1) u ∈ ((S.T t).lev j (c + 1 + 1) (by omega)).J := by sorry
