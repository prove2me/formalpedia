-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_lintegral_eq_normSq_det_mul_lintegral_mulVec
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:40.642716+00:00
-- url     : https://prove2.me/theorems/6bcaee15-544f-4856-acf3-76ce84c1346d
-- title:
--   Hua Int: lintegral eq norm Sq det mul lintegral mul Vec
-- statement:
--   The Hua Int construction uses the lintegral eq norm Sq det mul lintegral mul Vec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralLinearChangeVariablesComplex.lean#L13-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralLinearChangeVariablesComplex.lean#L13-L30

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralLinearChangeVariablesComplex
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_eq_normSq_det_mul_lintegral_mulVec (n : ℕ) (D : Matrix (Fin n) (Fin n) ℂ)
    (hD : Matrix.det D ≠ 0) (g : (Fin n → ℂ) → ENNReal) (hg : Measurable g) :
    ∫⁻ u, g u = ENNReal.ofReal (Complex.normSq (Matrix.det D)) * ∫⁻ v, g (D *ᵥ v) := by sorry
