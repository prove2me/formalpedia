-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_commute_coeff_om
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.commute_coeff_om
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:09:45.776345+00:00
-- url     : https://prove2.me/theorems/007627c6-dce9-5723-a20e-fd05e20bd68b
-- title:
--   Cayley Om: commute coeff om
-- statement:
--   The Cayley Om construction uses the commute coeff om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L143-L150
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L143-L150

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Polynomial Formalism.REAL CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.commute_coeff_om (M : GMod n) (p : (Module.End ℂ (Fin n → M.V))[X])
    (h : ∀ y : ℂ, Commute (p.eval (algebraMap ℂ _ y)) (om M)) (k : ℕ) : Commute (p.coeff k) (om M) := by sorry
