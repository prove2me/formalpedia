-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_continuous_blkM
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.continuous_blkM
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:35:48.927809+00:00
-- url     : https://prove2.me/theorems/39d03649-6807-4c33-aac0-7d3c06573122
-- title:
--   Hua Int: continuous blk M
-- statement:
--   The Hua Int construction uses the continuous blk M property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousBlkM.lean#L33-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousBlkM.lean#L33-L42

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open MeasureTheory Matrix
open scoped ComplexConjugate

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.continuous_blkM {n : ℕ} :
    Continuous (fun x : Matrix (Fin n) (Fin n) ℂ × (Fin n → ℂ) × ℝ => blkM x.1 x.2.1 x.2.2) := by sorry
