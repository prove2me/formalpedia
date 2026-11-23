-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_exists_scalar_stabilizer_line
-- name    : GlobalTheory.CompanionTheory.GLFirstBasisOrbit.exists_scalar_stabilizer_line
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:05.579019+00:00
-- url     : https://prove2.me/theorems/da5a3919-4457-4efa-aa7f-65375d60a749
-- title:
--   GLFirst Basis Orbit: exists scalar stabilizer line
-- statement:
--   The GLFirst Basis Orbit construction uses the exists scalar stabilizer line property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L104-L117
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L104-L117

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

theorem GlobalTheory.CompanionTheory.GLFirstBasisOrbit.exists_scalar_stabilizer_line (g : GL (Fin (n + 1)) k)
    (h : gmap g (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n}) :
    ∃ s : k, s ≠ 0 ∧ g.val *ᵥ e0 k n = s • e0 k n := by sorry
