-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_continuousOn_deriv_param
-- name    : GlobalTheory.CompanionTheory.HolFamily.continuousOn_deriv_param
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:17.324472+00:00
-- url     : https://prove2.me/theorems/b6d5bfb8-4038-48e4-a862-4da0520bbb2d
-- title:
--   Hol Family: continuous On deriv param
-- statement:
--   The Hol Family construction uses the continuous On deriv param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AutomorphicFunctionalHolomorphicDerivative.lean#L8-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/AutomorphicFunctionalHolomorphicDerivative.lean#L8-L15

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_AutomorphicFunctionalHolomorphicDerivative
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Topology Filter
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolFamily

theorem GlobalTheory.CompanionTheory.HolFamily.continuousOn_deriv_param {G : Type} [TopologicalSpace G] {U : Set ℂ} (hU : IsOpen U)
    {E : ℂ → G → ℂ} (hd : ∀ g, DifferentiableOn ℂ (E · g) U)
    (hc : ContinuousOn (fun y : ℂ × G => E y.1 y.2) (U ×ˢ Set.univ)) :
    ContinuousOn (fun y : ℂ × G => deriv (E · y.2) y.1) (U ×ˢ Set.univ) := by sorry
