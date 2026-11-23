-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_mem_GL_image_hyperplane_iff
-- name    : GlobalTheory.CompanionTheory.GLFirstBasisOrbit.mem_GL_image_hyperplane_iff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:41.509212+00:00
-- url     : https://prove2.me/theorems/a049c4c7-6a76-4827-9959-a23f87bd27f8
-- title:
--   GLFirst Basis Orbit: mem GL image hyperplane iff
-- statement:
--   The GLFirst Basis Orbit construction uses the mem GL image hyperplane iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L98-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L98-L102

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

theorem GlobalTheory.CompanionTheory.GLFirstBasisOrbit.mem_GL_image_hyperplane_iff (g : GL (Fin (n + 1)) k) (a : Fin (n + 1) → k)
    (h : ∀ x, a ⬝ᵥ (g.val *ᵥ x) = x 0) (z : Fin (n + 1) → k) :
    z ∈ gmap g (H0 k n) ↔ a ⬝ᵥ z = 0 := by sorry
