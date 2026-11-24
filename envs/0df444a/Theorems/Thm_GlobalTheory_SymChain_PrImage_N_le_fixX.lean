-- Prove2me | Theorems.Thm_GlobalTheory_SymChain_PrImage_N_le_fixX
-- name    : GlobalTheory.SymChain.PrImage.N_le_fixX
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T22:35:53.472442+00:00
-- url     : https://prove2.me/theorems/99944f0a-a34e-4a06-bfd3-8841bc2a85e3
-- title:
--   Pr Image: N le fix X
-- statement:
--   The Pr Image construction uses the N le fix X property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainProjectedLevelOfPattern.lean#L29-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DecoratedLatticeProofs/SymmetricChainProjectedLevelOfPattern.lean#L29-L31

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_LatticeFrames_OnesRepresent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DecoratedLatticeProofs_SymmetricChainProjectedLevelOfPattern
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
open GlobalTheory GlobalTheory.SymChain GlobalTheory.SymChain.PrImage
variable {k : Type*} [Field k] {ι n : Type*} [Fintype ι] [DecidableEq ι] [Fintype n] [DecidableEq n] {c : ℕ}

theorem GlobalTheory.SymChain.PrImage.N_le_fixX : N k n c 1 ≤ fixX k n c := by sorry
