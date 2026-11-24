-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_inner_eq
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.inner_eq
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T12:15:07.948786+00:00
-- url     : https://prove2.me/theorems/0c87ba01-454a-482f-a49f-72154eff03cc
-- title:
--   Hua Int: inner eq
-- statement:
--   The Hua Int construction uses the inner eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HuaDeterminantIntegrableOfLt.lean#L27-L82
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HuaDeterminantIntegrableOfLt.lean#L27-L82

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetWEqNormSqDetOneAddIStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_OneLeDetWStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetWBlockMatrixFormulaStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralPowerLineScalingStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralLinearChangeVariablesComplexStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralComplexPowerFiniteStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianHaarBlockDecompositionStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HuaDeterminantIntegrableOfLt
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

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.inner_eq (n : ℕ) (s : ℝ) (hs : (n : ℝ) + 1 / 2 < s) : ∃ K : ENNReal, K ≠ ⊤ ∧
    ∀ b' : hermC n, ∫⁻ u : Fin n → ℂ, ∫⁻ d : ℝ,
      ENNReal.ofReal (detW (blk b' u d : Matrix (Fin (n+1)) (Fin (n+1)) ℂ) ^ (-s)) =
      K * ENNReal.ofReal (detW (b' : Matrix (Fin n) (Fin n) ℂ) ^ (-(s - 1))) := by sorry
