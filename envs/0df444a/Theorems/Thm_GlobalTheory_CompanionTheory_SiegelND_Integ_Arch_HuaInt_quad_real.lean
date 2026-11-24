-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_HuaInt_quad_real
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.quad_real
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T12:13:24.580515+00:00
-- url     : https://prove2.me/theorems/123c2221-dbf0-48ac-aec0-c7548e5c5d13
-- title:
--   Hua Int: quad real
-- statement:
--   The Hua Int construction uses the quad real property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DetWBlockMatrixFormula.lean#L63-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/DetWBlockMatrixFormula.lean#L63-L67

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

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.HuaInt.quad_real {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} (hb : b.IsHermitian) (v : Fin n → ℂ) :
    ((star v ⬝ᵥ (b *ᵥ v)).re : ℂ) = star v ⬝ᵥ (b *ᵥ v) := by sorry
