-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_GLFirstBasisOrbit_smul_mem_gmap
-- name    : GlobalTheory.CompanionTheory.GLFirstBasisOrbit.smul_mem_gmap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:06:16.141347+00:00
-- url     : https://prove2.me/theorems/e2aba6d3-a788-4c51-8490-01d80332c8a5
-- title:
--   GLFirst Basis Orbit: smul mem gmap
-- statement:
--   The GLFirst Basis Orbit construction uses the smul mem gmap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L25-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/MemRiemannRochSpaceIffRegularAtEverywhere.lean#L25-L27

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

theorem GlobalTheory.CompanionTheory.GLFirstBasisOrbit.smul_mem_gmap {N : ℕ} (g : GL (Fin N) k) (M : Submodule k (Fin N → k)) (x : Fin N → k) :
    g.val *ᵥ x ∈ gmap g M ↔ x ∈ M := by sorry
