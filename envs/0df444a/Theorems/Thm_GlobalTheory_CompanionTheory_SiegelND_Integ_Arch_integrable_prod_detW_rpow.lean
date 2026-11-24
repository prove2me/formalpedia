-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_integrable_prod_detW_rpow
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T12:14:33.495047+00:00
-- url     : https://prove2.me/theorems/4634976d-fd99-40d4-a206-6f235c225cb0
-- title:
--   Arch: integrable prod det W rpow
-- statement:
--   The Arch construction uses the integrable prod det W rpow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductHuaDeterminantIntegrable.lean#L9-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductHuaDeterminantIntegrable.lean#L9-L19

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HuaDeterminantIntegrableOfLtStatement
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductHuaDeterminantIntegrable
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.integrable_prod_detW_rpow : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
    ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
    Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by sorry
