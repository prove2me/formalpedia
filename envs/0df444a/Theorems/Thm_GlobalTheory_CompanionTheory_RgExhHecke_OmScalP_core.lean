-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_OmScalP_core
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.core
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:59.50898+00:00
-- url     : https://prove2.me/theorems/61459e2b-72dc-4422-b239-784f1c3ec6d2
-- title:
--   Om Scal P: core
-- statement:
--   The Om Scal P construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean#L83-L130
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean#L83-L130

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.OmScalP
open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk

theorem GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.core {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (s : Fin n) (hS : ScalChar X χ)
    (hs : ∀ r, r ≠ s → χ r ≠ χ s) (g : Fin n → X.V)
    (h2 : om X (om X g - (χ s - cn n) • g) = (χ s - cn n) • (om X g - (χ s - cn n) • g)) :
    om X g - (χ s - cn n) • g = 0 := by sorry
