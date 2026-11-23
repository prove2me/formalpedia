-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeTransfer_hk_comm
-- name    : GlobalTheory.CompanionTheory.HeckeTransfer.hk_comm
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T09:58:47.87994+00:00
-- url     : https://prove2.me/theorems/891cf7e0-5027-4bb7-a062-e5f50e3d56f0
-- title:
--   Hecke Transfer: hk comm
-- statement:
--   The Hecke Transfer construction uses the hk comm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean#L104-L107
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/TransferStatementBis.lean#L104-L107

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

theorem GlobalTheory.CompanionTheory.HeckeTransfer.hk_comm (h : Hk K) (g : G) (f : (G ⧸ K) →₀ ℂ) :
    lam K g ((h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) f) = (h : Module.End ℂ ((G ⧸ K) →₀ ℂ)) (lam K g f) := by sorry
