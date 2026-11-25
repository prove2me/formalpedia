-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_stdOrd_pen
-- name    : GlobalTheory.SymChain.stdOrd_pen
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T10:38:33.124447+00:00
-- url     : https://prove2.me/theorems/e06e38d8-e8a5-5fe8-a772-891ec64f443a
-- title:
--   Sym Chain: std Ord pen
-- statement:
--   The Sym Chain construction uses the std Ord pen property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainOneCouplingCosetOfPattern.lean#L72-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainOneCouplingCosetOfPattern.lean#L72-L73

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainOneCouplingCosetOfPattern
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain
open GlobalTheory GlobalTheory.SymChain
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]
omit [Fintype t] [DecidableEq t]

theorem GlobalTheory.SymChain.stdOrd_pen (s : ℕ) : stdOrd (Fin κ) t s (0 + 1) rfl (.inl (.inr 0)) = .inr 0 := by sorry
