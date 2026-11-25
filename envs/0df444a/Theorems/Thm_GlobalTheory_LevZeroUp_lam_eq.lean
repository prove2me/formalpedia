-- Prove2me | Theorems.Thm_GlobalTheory_LevZeroUp_lam_eq
-- name    : GlobalTheory.LevZeroUp.lam_eq
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T10:25:45.736963+00:00
-- url     : https://prove2.me/theorems/1a268eb8-7cd6-4602-b32b-a07a323a6155
-- title:
--   Lev Zero Up: lam eq
-- statement:
--   The Lev Zero Up construction uses the lam eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LevelZeroUniformizerFrameUnipotentAndEmbedGL.lean#L103-L111
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/LevelZeroUniformizerFrameUnipotentAndEmbedGL.lean#L103-L111

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

theorem GlobalTheory.LevZeroUp.lam_eq (n : S.P.J) (hn : n.1 ∈ N k (Fin κ) (s + 1) (S.ρ + 1)) :
    ((S.P.lam n : ℂˣ) : ℂ) = (S.ψ (simpleSum (upZero S t n.1)) : ℂ) := by sorry
