-- Prove2me | Theorems.Thm_GlobalTheory_T_product_hua_determinant_integrable
-- name    : GlobalTheory.T.product_hua_determinant_integrable
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T12:36:44.492165+00:00
-- url     : https://prove2.me/theorems/d8f27eaa-dd2b-56c6-8b42-4e909f7ed02e
-- title:
--   T: product hua determinant integrable
-- statement:
--   The T construction uses the product hua determinant integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductHuaDeterminantIntegrableStatement.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ProductHuaDeterminantIntegrableStatement.lean#L8-L11

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductHuaDeterminantIntegrable
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ProductHuaDeterminantIntegrableStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.product_hua_determinant_integrable : ∀ (W : Type) [Fintype W] (n : ℕ) (s : ℝ), (n : ℝ) - 1 / 2 < s →
  ∀ ν : Measure (W → hermC n), ν.IsAddHaarMeasure →
  Integrable (fun b : W → hermC n => ∏ w, detW (b w : Matrix (Fin n) (Fin n) ℂ) ^ (-s)) ν := by sorry
