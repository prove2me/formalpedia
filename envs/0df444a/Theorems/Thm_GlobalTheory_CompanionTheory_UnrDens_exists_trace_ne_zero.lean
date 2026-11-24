-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_UnrDens_exists_trace_ne_zero
-- name    : GlobalTheory.CompanionTheory.UnrDens.exists_trace_ne_zero
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T12:19:39.937795+00:00
-- url     : https://prove2.me/theorems/dbbf3342-afae-4f3f-b6b6-8ffa44a84262
-- title:
--   Unr Dens: exists trace ne zero
-- statement:
--   The Unr Dens construction uses the exists trace ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianSpaceAnisotropicUnit.lean#L8-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HermitianSpaceAnisotropicUnit.lean#L8-L20

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ResAlgSplitTwo
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HermitianSpaceAnisotropicUnit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open PositivityTheory.PfSWUS.Loc GlobalTheory.CompanionTheory.UnrDens
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.UnrDens

theorem GlobalTheory.CompanionTheory.UnrDens.exists_trace_ne_zero {E : Type} [CommRing E] {τ : E →+* E} {q : ℕ} {ε : ℤ}
    (hE : ResAlg E τ q ε) {a : E} (ha : a ≠ 0) : ∃ c : E, c * a + τ (c * a) ≠ 0 := by sorry
