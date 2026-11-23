-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_mem_stabV
-- name    : GlobalTheory.CompanionTheory.GLFirstBasisOrbit.mem_stabV
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:07:02.616262+00:00
-- url     : https://prove2.me/theorems/17821323-f1ae-4fdb-b277-ca1dfe8eb6a0
-- title:
--   GLFirst Basis Orbit: mem stab V
-- statement:
--   The GLFirst Basis Orbit construction uses the mem stab V property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L135-L137
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L135-L137

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
variable {V Γ : Type} [AddCommGroup V] [Module ℂ V] [Group Γ]

theorem GlobalTheory.CompanionTheory.GLFirstBasisOrbit.mem_stabV (red : Γ →* GL (Fin (n + 1)) k) (ρ : Γ →* Module.End ℂ V) (y : V) :
    y ∈ stabV red ρ ↔
      ∀ γ, gmap (red γ) (Submodule.span k {e0 k n}) = Submodule.span k {e0 k n} → ρ γ y = y := by sorry
