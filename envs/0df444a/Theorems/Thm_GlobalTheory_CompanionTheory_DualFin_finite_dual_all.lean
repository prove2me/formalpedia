-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_DualFin_finite_dual_all
-- name    : GlobalTheory.CompanionTheory.DualFin.finite_dual_all
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T11:37:24.139134+00:00
-- url     : https://prove2.me/theorems/521e4acf-0808-4468-ba53-e4c52466d92d
-- title:
--   Dual Fin: finite dual all
-- statement:
--   The Dual Fin construction uses the finite dual all property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDualAll.lean#L5-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/FiniteDualAll.lean#L5-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_FiniteDualAll
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.DualFin

theorem GlobalTheory.CompanionTheory.DualFin.finite_dual_all : ∀ (R M : Type) [CommRing R] [Finite R] [AddCommGroup M] [Module R M] [Finite M], Finite (Module.Dual R M) := by sorry
