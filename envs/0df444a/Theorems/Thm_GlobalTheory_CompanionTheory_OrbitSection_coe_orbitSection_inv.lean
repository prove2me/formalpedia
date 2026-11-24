-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_coe_orbitSection_inv
-- name    : GlobalTheory.CompanionTheory.OrbitSection.coe_orbitSection_inv
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:53:38.52295+00:00
-- url     : https://prove2.me/theorems/5464bd8d-7936-4c93-a5c6-fb63b8b85a1d
-- title:
--   Orbit Section: coe orbit Section inv
-- statement:
--   The Orbit Section construction uses the coe orbit Section inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean#L57-L60
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean#L57-L60

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

theorem GlobalTheory.CompanionTheory.OrbitSection.coe_orbitSection_inv (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) (h1 : ξ j ≠ 0) :
    ((orbitSection j ζ ξ)⁻¹ : (Matrix (Fin n) (Fin n) k)ˣ).val = shear j (-(ξ j)⁻¹) ζ ξ := by sorry
