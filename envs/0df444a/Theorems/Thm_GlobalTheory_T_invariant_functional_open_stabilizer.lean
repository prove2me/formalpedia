-- Prove2me | Theorems.Thm_GlobalTheory_T_invariant_functional_open_stabilizer
-- name    : GlobalTheory.T.invariant_functional_open_stabilizer
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:37:27.231142+00:00
-- url     : https://prove2.me/theorems/3fd58fdb-339a-4890-997e-2b83b65446e8
-- title:
--   T: invariant functional open stabilizer
-- statement:
--   The T construction uses the invariant functional open stabilizer property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalOpenStabilizerStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/InvariantFunctionalOpenStabilizerStatement.lean#L5-L6

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalOpenStabilizer
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_InvariantFunctionalOpenStabilizerStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.invariant_functional_open_stabilizer : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G), IsOpen (K : Set G) → ∀ l : Module.Dual ℂ V, (∀ x ∈ K, l ∘ₗ ρ x = l) → IsOpen {g : G | l ∘ₗ ρ g = l} := by sorry
