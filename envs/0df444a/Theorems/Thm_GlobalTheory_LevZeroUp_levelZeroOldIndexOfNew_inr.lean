-- Prove2me | Theorems.Thm_GlobalTheory_LevZeroUp_levelZeroOldIndexOfNew_inr
-- name    : GlobalTheory.LevZeroUp.levelZeroOldIndexOfNew_inr
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T10:21:06.917704+00:00
-- url     : https://prove2.me/theorems/f25ba557-be99-49f5-80f6-1ab0e724de15
-- title:
--   Lev Zero Up: level Zero Old Index Of New inr
-- statement:
--   The Lev Zero Up construction uses the level Zero Old Index Of New inr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LevelZeroUniformizerFrameUnipotentAndEmbedGL.lean#L25-L29
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LevelZeroUniformizerFrameUnipotentAndEmbedGL.lean#L25-L29

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_UpZeroMemLev
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_MemLevelIffSymmetricPositionEntryPattern
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_LevelZeroUniformizerFrameUnipotentAndEmbedGL
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel Matrix
open scoped Classical
noncomputable section
open GlobalTheory GlobalTheory.LevZeroUp
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.LevZeroGen GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

theorem GlobalTheory.LevZeroUp.levelZeroOldIndexOfNew_inr (i : Fin (s + 1)) : back (κ := κ) t (.inr i) = .inr i := by sorry
