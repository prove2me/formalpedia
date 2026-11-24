-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_OrbitSection_continuousOn_shear
-- name    : GlobalTheory.CompanionTheory.OrbitSection.continuousOn_shear
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:53:41.678824+00:00
-- url     : https://prove2.me/theorems/b81c06a9-decc-4eea-9c11-d3fbacfc60d1
-- title:
--   Orbit Section: continuous On shear
-- statement:
--   The Orbit Section construction uses the continuous On shear property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean#L68-L73
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/LocalContinuousSectionVecMulOrbit.lean#L68-L73

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

theorem GlobalTheory.CompanionTheory.OrbitSection.continuousOn_shear (j : Fin n) (ζ : Fin n → k) {N : Set (Fin n → k)} {c : (Fin n → k) → k}
    (hc : ContinuousOn c N) : ContinuousOn (fun ξ => shear j (c ξ) ζ ξ) N := by sorry
