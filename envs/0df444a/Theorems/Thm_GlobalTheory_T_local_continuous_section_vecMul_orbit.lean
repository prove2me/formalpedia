-- Prove2me | Theorems.Thm_GlobalTheory_T_local_continuous_section_vecMul_orbit
-- name    : GlobalTheory.T.local_continuous_section_vecMul_orbit
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:35:14.042963+00:00
-- url     : https://prove2.me/theorems/84cf2580-32ca-4247-860f-41fde574f92b
-- title:
--   T: local continuous section vec Mul orbit
-- statement:
--   The T construction uses the local continuous section vec Mul orbit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbitStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbitStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbit
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_LocalContinuousSectionVecMulOrbitStatement
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
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.local_continuous_section_vecMul_orbit : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ) (ζ : Fin n → k), ζ ≠ 0 → ∃ N : Set (Fin n → k), IsOpen N ∧ ζ ∈ N ∧ ∃ f : (Fin n → k) → GL (Fin n) k, ContinuousOn f N ∧ f ζ = 1 ∧ ∀ ξ ∈ N, ζ ᵥ* (f ξ : Matrix (Fin n) (Fin n) k) = ξ := by sorry
