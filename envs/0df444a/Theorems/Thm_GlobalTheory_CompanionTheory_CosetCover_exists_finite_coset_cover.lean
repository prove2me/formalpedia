-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_CosetCover_exists_finite_coset_cover
-- name    : GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-24T11:34:27.142917+00:00
-- url     : https://prove2.me/theorems/cf35bd87-5b2f-43c6-9085-267663f9e3f8
-- title:
--   Coset Cover: exists finite coset cover
-- statement:
--   The Coset Cover construction uses the exists finite coset cover property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CompactSubgroupFiniteOpenCosets.lean#L5-L19
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CompactSubgroupFiniteOpenCosets.lean#L5-L19

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CompactSubgroupFiniteOpenCosets
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.CosetCover

theorem GlobalTheory.CompanionTheory.CosetCover.exists_finite_coset_cover :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (K₀ K : Subgroup G),
      IsCompact (K₀ : Set G) → IsOpen (K : Set G) →
        ∃ (d : ℕ) (c : Fin d → G), (∀ i, c i ∈ K₀) ∧ ∀ g ∈ K₀, ∃ i, ∃ κ ∈ K, g = κ * c i := by sorry
