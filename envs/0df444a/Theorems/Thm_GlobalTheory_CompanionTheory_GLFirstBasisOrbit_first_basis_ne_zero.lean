-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_first_basis_ne_zero
-- name    : GlobalTheory.CompanionTheory.GLFirstBasisOrbit.first_basis_ne_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:26.187615+00:00
-- url     : https://prove2.me/theorems/70d03d85-2086-4b31-ad04-b4ece2dd7823
-- title:
--   GLFirst Basis Orbit: first basis ne zero
-- statement:
--   The GLFirst Basis Orbit construction uses the first basis ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L56-L59
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L56-L59

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

theorem GlobalTheory.CompanionTheory.GLFirstBasisOrbit.first_basis_ne_zero : e0 k n ≠ 0 := by sorry
