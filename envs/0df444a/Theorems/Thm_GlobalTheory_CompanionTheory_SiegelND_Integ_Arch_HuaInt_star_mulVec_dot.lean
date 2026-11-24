-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_star_mulVec_dot
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.star_mulVec_dot
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:58.261717+00:00
-- url     : https://prove2.me/theorems/43f86395-ad67-4cbd-a9a8-906ffe884033
-- title:
--   Hua Int: star mul Vec dot
-- statement:
--   The Hua Int construction uses the star mul Vec dot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DetWBlockMatrixFormula.lean#L69-L79
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DetWBlockMatrixFormula.lean#L69-L79

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_DetWBlockMatrixFormula
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

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.star_mulVec_dot {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian)
    (v : Fin n → ℂ) :
    star ((1 + Complex.I • b) *ᵥ v) ⬝ᵥ v =
      ((∑ i, Complex.normSq (v i) : ℝ) : ℂ) - Complex.I * ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) := by sorry
