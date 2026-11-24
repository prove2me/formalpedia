-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_phi_phi
-- name    : GlobalTheory.CompanionTheory.HeckeTransfer.phi_phi
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T11:47:07.604062+00:00
-- url     : https://prove2.me/theorems/7399c6bc-e6ff-4bbf-8cc1-d016636513c3
-- title:
--   Hecke Transfer: phi phi
-- statement:
--   The Hecke Transfer construction uses the phi phi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean#L115-L127
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean#L115-L127

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

theorem GlobalTheory.CompanionTheory.HeckeTransfer.phi_phi (hv : ∀ k ∈ K, σ k v = v) (h : Hk K) (f : (G ⧸ K) →₀ ℂ) :
    phi K σ (phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (dlt K))) f =
      phi K σ v ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) f) := by sorry
