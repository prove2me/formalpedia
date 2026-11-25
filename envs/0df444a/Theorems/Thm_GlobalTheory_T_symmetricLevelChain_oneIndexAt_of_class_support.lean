-- Prove2me | Theorems.Thm_GlobalTheory_T_symmetricLevelChain_oneIndexAt_of_class_support
-- name    : GlobalTheory.T.symmetricLevelChain_oneIndexAt_of_class_support
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:40:26.296878+00:00
-- url     : https://prove2.me/theorems/446e06f9-b269-5e57-8c2c-61727850ae4d
-- title:
--   T: symmetric Level Chain one Index At of class support
-- statement:
--   The T construction uses the symmetric Level Chain one Index At of class support property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainOneIndexAtOfClassSupportStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricLevelChainOneIndexAtOfClassSupportStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainOneIndexAtOfClassSupport
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_AllPositions
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricLevelChainOneIndexAtOfClassSupportStatement
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

theorem GlobalTheory.T.symmetricLevelChain_oneIndexAt_of_class_support : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν → ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t], S.ClassAt t ν → S.SupportAt t → S.OneIndexAt t ν := by sorry
