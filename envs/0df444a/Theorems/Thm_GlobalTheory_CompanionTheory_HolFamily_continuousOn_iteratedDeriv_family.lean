-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HolFamily_continuousOn_iteratedDeriv_family
-- name    : GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T11:48:49.805782+00:00
-- url     : https://prove2.me/theorems/472e885f-8280-4c71-9895-ac27caae3f2e
-- title:
--   Hol Family: continuous On iterated Deriv family
-- statement:
--   The Hol Family construction uses the continuous On iterated Deriv family property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousOnIteratedDerivFamily.lean#L71-L88
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/ContinuousOnIteratedDerivFamily.lean#L71-L88

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

theorem GlobalTheory.CompanionTheory.HolFamily.continuousOn_iteratedDeriv_family :
    ∀ (P : Type) [TopologicalSpace P] (U : Set ℂ), IsOpen U → ∀ H : P → ℂ → ℂ,
      ContinuousOn (fun q : P × ℂ => H q.1 q.2) (Set.univ ×ˢ U) →
      (∀ p, DifferentiableOn ℂ (H p) U) →
        ∀ r : ℕ, ContinuousOn (fun q : P × ℂ => iteratedDeriv r (H q.1) q.2) (Set.univ ×ˢ U) := by sorry
