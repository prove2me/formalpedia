-- Prove2me | Theorems.Thm_GlobalTheory_T_continuous_iteratedDeriv_holomorphic_family
-- name    : GlobalTheory.T.continuous_iteratedDeriv_holomorphic_family
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:28:08.286339+00:00
-- url     : https://prove2.me/theorems/cc9a64e1-ab85-45ab-ba37-e2cac26950e3
-- title:
--   T: continuous iterated Deriv holomorphic family
-- statement:
--   The T construction uses the continuous iterated Deriv holomorphic family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousIteratedDerivHolomorphicFamilyStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousIteratedDerivHolomorphicFamilyStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousIteratedDerivHolomorphicFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousIteratedDerivHolomorphicFamilyStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
set_option maxHeartbeats 1000000

theorem GlobalTheory.T.continuous_iteratedDeriv_holomorphic_family : ∀ {G : Type} [TopologicalSpace G] (U : Set ℂ) (Ê : ℂ → G → ℂ), IsOpen U → (∀ g, DifferentiableOn ℂ (Ê · g) U) → ContinuousOn (fun y : ℂ × G => Ê y.1 y.2) (U ×ˢ Set.univ) → ∀ z ∈ U, ∀ j : ℕ, Continuous fun g => iteratedDeriv j (Ê · g) z := by sorry
