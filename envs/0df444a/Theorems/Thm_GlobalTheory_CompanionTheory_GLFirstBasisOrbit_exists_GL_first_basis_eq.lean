-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_exists_GL_first_basis_eq
-- name    : GlobalTheory.CompanionTheory.GLFirstBasisOrbit.exists_GL_first_basis_eq
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:04.791162+00:00
-- url     : https://prove2.me/theorems/72bf4fad-3e4d-45c4-93db-6b7611ea9947
-- title:
--   GLFirst Basis Orbit: exists GL first basis eq
-- statement:
--   The GLFirst Basis Orbit construction uses the exists GL first basis eq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L67-L83
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L67-L83

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

theorem GlobalTheory.CompanionTheory.GLFirstBasisOrbit.exists_GL_first_basis_eq (x : Fin (n + 1) → k) (hx : x ≠ 0) :
    ∃ g : GL (Fin (n + 1)) k, g.val *ᵥ e0 k n = x := by sorry
