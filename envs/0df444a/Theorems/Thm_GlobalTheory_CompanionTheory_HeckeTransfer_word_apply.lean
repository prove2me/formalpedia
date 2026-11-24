-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_word_apply
-- name    : GlobalTheory.CompanionTheory.HeckeTransfer.word_apply
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T11:46:24.640307+00:00
-- url     : https://prove2.me/theorems/3cf0c412-be3e-48e7-a310-79ba42f076f7
-- title:
--   Hecke Transfer: word apply
-- statement:
--   The Hecke Transfer construction uses the word apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean#L155-L169
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean#L155-L169

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_UnitaryAdmissibility_ArchimedeanUnitaryDual_InhabitedFinite
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeOperatorsSpanAndFaithfulStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_TransferStatementBis
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_cons
import Theorems.Thm_CompanionTheory_D_gk_admitted_word_nil
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.gk.admitted.word_cons
attribute [local simp] CompanionTheory.D.gk.admitted.word_nil


set_option autoImplicit false
open CompanionTheory.Rg.Fl
open CompanionTheory.D.gk.admitted (stdPoly word word_nil word_cons)
noncomputable section
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeTransfer
variable {G H : Type} [Group G] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
variable {K : Subgroup G} {σ : G →* (H →L[ℂ] H)} {v : H}

theorem GlobalTheory.CompanionTheory.HeckeTransfer.word_apply {E : H →L[ℂ] H} (hA : IsAvg σ K E) (b : G → Hk K)
    (hb : ∀ (u : H), (∀ k ∈ K, σ k u = u) → ∀ g, E (σ g u) = phi K σ u ((b g : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)))
    (hv : ∀ k ∈ K, σ k v = v) (l : List G) :
    word E (l.map fun g => σ g) v =
      phi K σ v ((((l.map b).reverse.prod : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by sorry
