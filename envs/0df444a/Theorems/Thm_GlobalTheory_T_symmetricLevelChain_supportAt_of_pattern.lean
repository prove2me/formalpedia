-- Prove2me | Theorems.Thm_GlobalTheory_T_symmetricLevelChain_supportAt_of_pattern
-- name    : GlobalTheory.T.symmetricLevelChain_supportAt_of_pattern
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:25.235489+00:00
-- url     : https://prove2.me/theorems/7b6cfd1a-db41-5071-90de-4624c16653f1
-- title:
--   T: symmetric Level Chain support At of pattern
-- statement:
--   The T construction uses the symmetric Level Chain support At of pattern property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainSupportAtOfPatternStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainSupportAtOfPatternStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainSupportAtOfPattern
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainSupportAtOfPatternStatement
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

theorem GlobalTheory.T.symmetricLevelChain_supportAt_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.Pattern t → S.SupportAt t := by sorry
