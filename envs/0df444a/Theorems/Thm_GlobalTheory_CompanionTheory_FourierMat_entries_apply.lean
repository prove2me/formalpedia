-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_FourierMat_entries_apply
-- name    : GlobalTheory.CompanionTheory.FourierMat.entries_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T11:41:24.478735+00:00
-- url     : https://prove2.me/theorems/d5f2506b-bfd0-4020-9ede-fd20b1684646
-- title:
--   Fourier Mat: entries apply
-- statement:
--   The Fourier Mat construction uses the entries apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInjectiveMatrixSpace.lean#L18-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FourierInjectiveMatrixSpace.lean#L18-L19

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FourierInjectiveMatrixSpace
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory
open scoped Matrix FourierTransform InnerProductSpace ComplexConjugate
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.FourierMat

theorem GlobalTheory.CompanionTheory.FourierMat.entries_apply (m n : ℕ) (u : Fin m → Fin n → ℂ) (p : Fin m × Fin n) :
    entries m n u p = u p.1 p.2 := by sorry
