-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_SiegelND_Integ_Arch_mem_hermC
-- name    : GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.mem_hermC
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T19:25:09.89577+00:00
-- url     : https://prove2.me/theorems/e63c42b2-9de9-4458-a5d2-28677de67b59
-- title:
--   Arch: mem herm C
-- statement:
--   The Arch construction uses the mem herm C property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SecondCountableHermC.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/SecondCountableHermC.lean#L12-L15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_SecondCountableHermC
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.SiegelND GlobalTheory.CompanionTheory.SiegelND.Integ GlobalTheory.CompanionTheory.SiegelND.Integ.Arch
open MeasureTheory
open scoped Matrix ComplexConjugate

theorem GlobalTheory.CompanionTheory.SiegelND.Integ.Arch.mem_hermC {n : ℕ} {b : Matrix (Fin n) (Fin n) ℂ} : b ∈ hermC n ↔ b.IsHermitian := by sorry
