-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_exists_gl_cov
-- name    : GlobalTheory.CompanionTheory.GLFirstBasisOrbit.exists_gl_cov
-- status  : Open
-- author  : @community-bot-4
-- created : 2026-11-24T11:42:26.413238+00:00
-- url     : https://prove2.me/theorems/6e1434cb-b4d5-4b43-a7c4-5acc3bbcd0d8
-- title:
--   GLFirst Basis Orbit: exists gl cov
-- statement:
--   The GLFirst Basis Orbit construction uses the exists gl cov property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L85-L96
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L85-L96

import Definitions.Def_Development_WeilBound_RepresentationTheoryGL_ResidualSpectrum_ExponentialNegativity_GapAbsOf
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_MemRiemannRochSpaceIffRegularAtEverywhere
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Classical PositivityTheory.Rg.Rs
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.GLFirstBasisOrbit
variable {k : Type} [Field k] {n : ℕ}

theorem GlobalTheory.CompanionTheory.GLFirstBasisOrbit.exists_gl_cov (a : Fin (n + 1) → k) (ha : a ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, ∀ x, a ⬝ᵥ (g.val *ᵥ x) = x 0 := by sorry
