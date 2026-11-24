-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_haar_blocks
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T12:13:46.358167+00:00
-- url     : https://prove2.me/theorems/723b9b8b-0342-4e8d-91f4-0ebe859d88a5
-- title:
--   Hua Int: haar blocks
-- statement:
--   The Hua Int construction uses the haar blocks property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianHaarBlockDecomposition.lean#L100-L124
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianHaarBlockDecomposition.lean#L100-L124

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianHaarBlockDecomposition
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
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.haar_blocks (n : ℕ) (ν : Measure (hermC (n + 1))) (ν' : Measure (hermC n))
    (hν : ν.IsAddHaarMeasure) (hν' : ν'.IsAddHaarMeasure) :
    ∃ c : ENNReal, c ≠ ⊤ ∧ ∀ F : hermC (n + 1) → ENNReal, Measurable F →
      ∫⁻ b, F b ∂ν = c * ∫⁻ b', ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ, F (blk b' u d) ∂volume ∂volume ∂ν' := by sorry
