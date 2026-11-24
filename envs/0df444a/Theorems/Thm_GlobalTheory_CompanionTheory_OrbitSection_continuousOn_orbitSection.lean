-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_continuousOn_orbitSection
-- name    : GlobalTheory.CompanionTheory.OrbitSection.continuousOn_orbitSection
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:53:39.805821+00:00
-- url     : https://prove2.me/theorems/435cbaa3-9018-440e-a5de-89170df902b5
-- title:
--   Orbit Section: continuous On orbit Section
-- statement:
--   The Orbit Section construction uses the continuous On orbit Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean#L75-L84
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean#L75-L84

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.OrbitSection
variable {k : Type} [Field k] [TopologicalSpace k] [IsTopologicalDivisionRing k] {n : ℕ}

theorem GlobalTheory.CompanionTheory.OrbitSection.continuousOn_orbitSection (j : Fin n) (ζ : Fin n → k) (h0 : ζ j ≠ 0) :
    ContinuousOn (orbitSection j ζ) {ξ | ξ j ≠ 0} := by sorry
