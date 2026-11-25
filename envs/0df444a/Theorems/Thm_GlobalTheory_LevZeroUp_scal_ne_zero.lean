-- Prove2me | Theorems.Thm_GlobalTheory_LevZeroUp_scal_ne_zero
-- name    : GlobalTheory.LevZeroUp.scal_ne_zero
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T10:20:16.008994+00:00
-- url     : https://prove2.me/theorems/f1e99ec4-b612-5874-9b07-a3d72df9d4e2
-- title:
--   Lev Zero Up: scal ne zero
-- statement:
--   The Lev Zero Up construction uses the scal ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LevelZeroUniformizerFrameUnipotentAndEmbedGL.lean#L31-L32
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LevelZeroUniformizerFrameUnipotentAndEmbedGL.lean#L31-L32

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

theorem GlobalTheory.LevZeroUp.scal_ne_zero (ϖ : kˣ) (r : XIx (Fin κ) t 0 ⊕ Fin (s + 1)) : scal t ϖ r ≠ 0 := by sorry
