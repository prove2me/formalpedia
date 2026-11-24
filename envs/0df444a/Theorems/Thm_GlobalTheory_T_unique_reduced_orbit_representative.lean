-- Prove2me | Theorems.Thm_GlobalTheory_T_unique_reduced_orbit_representative
-- name    : GlobalTheory.T.unique_reduced_orbit_representative
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T21:00:45.963118+00:00
-- url     : https://prove2.me/theorems/cb5e873c-b537-47d4-bd23-2baccb77d8fa
-- title:
--   T: unique reduced orbit representative
-- statement:
--   The T construction uses the unique reduced orbit representative property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/UniqueReducedOrbitRepresentativeStatement.lean#L5-L8
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AutomorphicSpectrum/Proofs/GlobalProofs/UniqueReducedOrbitRepresentativeStatement.lean#L5-L8

import Mathlib
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_UniqueReducedOrbitRepresentative
import Definitions.Def_Development_AutomorphicSpectrum_Proofs_GlobalProofs_UniqueReducedOrbitRepresentativeStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.unique_reduced_orbit_representative : ∀ {G M : Type} [Group G] [Monoid M] (φ : G →* M) (f : G →* ℝ), (∀ g, 0 < f g) → Function.Injective f → ∀ (D : Set M),
    {g : G | ∃ x ∈ D, φ g * x ∈ D}.Finite → ∀ (x : M), (∃ g, φ g * x ∈ D) →
    ∃! g, φ g * x ∈ {y ∈ D | ∀ g' : G, f g' < 1 → φ g' * y ∉ D} := by sorry
