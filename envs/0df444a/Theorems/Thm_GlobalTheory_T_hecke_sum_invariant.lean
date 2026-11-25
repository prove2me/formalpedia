-- Prove2me | Theorems.Thm_GlobalTheory_T_hecke_sum_invariant
-- name    : GlobalTheory.T.hecke_sum_invariant
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:33:02.525632+00:00
-- url     : https://prove2.me/theorems/0b62989c-0ec3-4ec4-9bd7-b3bf5aff7834
-- title:
--   T: hecke sum invariant
-- statement:
--   The T construction uses the hecke sum invariant property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeSumInvariantStatement.lean#L6-L7
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/BlockDecomposition/HeckeSumInvariantStatement.lean#L6-L7

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeSumInvariant
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_Foundations_SmoothPartStable
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_TwistedInnerProducts_IsUnitarisableOfCharIff
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_BlockDecomposition_HeckeSumInvariantStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.hecke_sum_invariant : ∀ (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (K : Subgroup G) (f : G → ℂ), (Function.support fun q : G ⧸ K => f q.out).Finite → (∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) → ∀ v : V, (∀ k ∈ K, ρ k v = v) → ∀ k ∈ K, ρ k (∑ᶠ q : G ⧸ K, f q.out • ρ q.out v) = ∑ᶠ q : G ⧸ K, f q.out • ρ q.out v := by sorry
