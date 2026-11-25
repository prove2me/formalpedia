-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_CayleyOm_root
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.root
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:09:24.330206+00:00
-- url     : https://prove2.me/theorems/48e63bf5-9f40-5605-a50c-d86016211be8
-- title:
--   Cayley Om: root
-- statement:
--   The Cayley Om construction uses the root property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L152-L181
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/CayleyHamiltonStatement.lean#L152-L181

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.CayleyOm.root (H : QdetTens) (M : GMod n) (c : ℂ) (pC : (Module.End ℂ (Fin n → M.V))[X])
    (hC : ∀ y : ℂ, pC.eval (algebraMap ℂ _ y) = (qdet M.E (y + c)).compLeft (Fin n)) :
    pC.eval (-om M - algebraMap ℂ _ c) = 0 := by sorry
