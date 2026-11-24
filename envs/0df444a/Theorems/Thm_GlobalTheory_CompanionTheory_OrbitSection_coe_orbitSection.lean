-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_coe_orbitSection
-- name    : GlobalTheory.CompanionTheory.OrbitSection.coe_orbitSection
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:53:03.624853+00:00
-- url     : https://prove2.me/theorems/6cf45f4b-dbcb-4456-ac14-bf0890d04de0
-- title:
--   Orbit Section: coe orbit Section
-- statement:
--   The Orbit Section construction uses the coe orbit Section property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean#L53-L55
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean#L53-L55

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
variable {k : Type} [Field k] {n : ℕ}

theorem GlobalTheory.CompanionTheory.OrbitSection.coe_orbitSection (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    (orbitSection j ζ ξ : Matrix (Fin n) (Fin n) k) = shear j (ζ j)⁻¹ ζ ξ := by sorry
