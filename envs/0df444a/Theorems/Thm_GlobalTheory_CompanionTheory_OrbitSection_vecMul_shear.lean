-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_vecMul_shear
-- name    : GlobalTheory.CompanionTheory.OrbitSection.vecMul_shear
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:53:38.962873+00:00
-- url     : https://prove2.me/theorems/4576a41b-c736-4af1-82d4-d77e475a7875
-- title:
--   Orbit Section: vec Mul shear
-- statement:
--   The Orbit Section construction uses the vec Mul shear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean#L34-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean#L34-L40

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

theorem GlobalTheory.CompanionTheory.OrbitSection.vecMul_shear (j : Fin n) (ζ ξ : Fin n → k) (h0 : ζ j ≠ 0) :
    ζ ᵥ* shear j (ζ j)⁻¹ ζ ξ = ξ := by sorry
