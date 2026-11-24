-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_lintegral_one_add_normSq_rpow_ne_top
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:06.645012+00:00
-- url     : https://prove2.me/theorems/d937cc30-f2e0-4f0f-b9fd-05ad3a505cb3
-- title:
--   Hua Int: lintegral one add norm Sq rpow ne top
-- statement:
--   The Hua Int construction uses the lintegral one add norm Sq rpow ne top property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralComplexPowerFinite.lean#L9-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LintegralComplexPowerFinite.lean#L9-L34

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousBlkM
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LintegralComplexPowerFinite
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

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.lintegral_one_add_normSq_rpow_ne_top :
    ∀ (n : ℕ) (t : ℝ), (n : ℝ) < t →
    ∫⁻ v : Fin n → ℂ, ENNReal.ofReal ((1 + ∑ i, Complex.normSq (v i)) ^ (-t)) ≠ ⊤ := by sorry
