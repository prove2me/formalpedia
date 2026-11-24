-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeBasis_exists_mem_span_delta
-- name    : GlobalTheory.CompanionTheory.HeckeBasis.exists_mem_span_delta
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:45:32.02445+00:00
-- url     : https://prove2.me/theorems/d25f8ccf-e4b3-4ce4-87e0-f97920688f97
-- title:
--   Hecke Basis: exists mem span delta
-- statement:
--   The Hecke Basis construction uses the exists mem span delta property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithful.lean#L148-L193
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeOperatorsSpanAndFaithful.lean#L148-L193

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithful
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory.Rg.Fl
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeBasis
variable {G : Type} [Group G] (K : Subgroup G)
variable {K}
variable (K)
variable {K}
variable (K)
variable {K}

theorem GlobalTheory.CompanionTheory.HeckeBasis.exists_mem_span_delta (hK : IsHeckePair K) (n : ℕ) :
    ∀ u : (G ⧸ K) →₀ ℂ, IsFixed K u → u.support.card ≤ n →
      ∃ t ∈ Submodule.span ℂ (Set.range (heckeOp hK)),
        (t : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (delta K) = u := by sorry
