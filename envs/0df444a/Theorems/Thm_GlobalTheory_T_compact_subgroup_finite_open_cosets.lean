-- Prove2me | Theorems.Thm_GlobalTheory_T_compact_subgroup_finite_open_cosets
-- name    : GlobalTheory.T.compact_subgroup_finite_open_cosets
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T20:30:06.242153+00:00
-- url     : https://prove2.me/theorems/a9433fd4-94e5-4aeb-b2f7-6edd00eee219
-- title:
--   T: compact subgroup finite open cosets
-- statement:
--   The T construction uses the compact subgroup finite open cosets property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CompactSubgroupFiniteOpenCosetsStatement.lean#L5-L6
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CompactSubgroupFiniteOpenCosetsStatement.lean#L5-L6

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactSubgroupFiniteOpenCosets
import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactSubgroupFiniteOpenCosetsStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false

set_option maxHeartbeats 1000000

theorem GlobalTheory.T.compact_subgroup_finite_open_cosets : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G), IsCompact (K₀ : Set G) → IsOpen (K : Set G) → ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by sorry
