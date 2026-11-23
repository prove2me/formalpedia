-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_mem_riemannRochSpace_iff_regularAt_everywhere
-- name    : GlobalTheory.CompanionTheory.GLFirstBasisOrbit.mem_riemannRochSpace_iff_regularAt_everywhere
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:20.651863+00:00
-- url     : https://prove2.me/theorems/5dcb9058-f4ab-4599-876d-4483935da545
-- title:
--   GLFirst Basis Orbit: mem riemann Roch Space iff regular At everywhere
-- statement:
--   The GLFirst Basis Orbit construction uses the mem riemann Roch Space iff regular At everywhere property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L64-L65
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L64-L65

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

theorem GlobalTheory.CompanionTheory.GLFirstBasisOrbit.mem_riemannRochSpace_iff_regularAt_everywhere (x : Fin (n + 1) → k) : x ∈ H0 k n ↔ x 0 = 0 := by sorry
