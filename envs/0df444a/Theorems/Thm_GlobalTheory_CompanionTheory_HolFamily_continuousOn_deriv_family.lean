-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_continuousOn_deriv_family
-- name    : GlobalTheory.CompanionTheory.HolFamily.continuousOn_deriv_family
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T23:13:06.902882+00:00
-- url     : https://prove2.me/theorems/1a983c7d-91e1-4c87-b6f4-2e7ad20c1e5e
-- title:
--   Hol Family: continuous On deriv family
-- statement:
--   The Hol Family construction uses the continuous On deriv family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousOnIteratedDerivFamily.lean#L7-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousOnIteratedDerivFamily.lean#L7-L69

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_ContinuousOnIteratedDerivFamily
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Filter Topology
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HolFamily

theorem GlobalTheory.CompanionTheory.HolFamily.continuousOn_deriv_family (P : Type) [TopologicalSpace P] (U : Set ℂ) (hU : IsOpen U)
    (H : P → ℂ → ℂ) (hc : ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U))
    (hd : ∀ p, DifferentiableOn ℂ (H p) U) :
    ContinuousOn (fun q : P × ℂ => deriv (H q.1) q.2) (Set.univ ×ˢ U) := by sorry
