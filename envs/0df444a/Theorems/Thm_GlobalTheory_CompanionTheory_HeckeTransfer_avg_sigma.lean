-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_avg_sigma
-- name    : GlobalTheory.CompanionTheory.HeckeTransfer.avg_sigma
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:19.766049+00:00
-- url     : https://prove2.me/theorems/24f859be-fe08-4fe3-a336-19fcf0a6f994
-- title:
--   Hecke Transfer: avg sigma
-- statement:
--   The Hecke Transfer construction uses the avg sigma property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean#L129-L153
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean#L129-L153

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

theorem GlobalTheory.CompanionTheory.HeckeTransfer.avg_sigma {E : H →L[ℂ] H} (hA : IsAvg σ K E) (hv : ∀ k ∈ K, σ k v = v) (g : G) (T : Hk K)
    (S : Finset (G ⧸ K)) (hS : (↑S : Set (G ⧸ K)) = MulAction.orbit K (g : G ⧸ K))
    (hT : (T : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K) = ∑ y ∈ S, Finsupp.single y (1 : ℂ)) :
    E (σ g v) = phi K σ v ((((S.card : ℂ)⁻¹ • T : Hk K) : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K)) := by sorry
