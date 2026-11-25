-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_OmScalP_tens_apply
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.tens_apply
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:30:34.697981+00:00
-- url     : https://prove2.me/theorems/5806a12c-0176-4db4-a84f-d48aef875d53
-- title:
--   Om Scal P: tens apply
-- statement:
--   The Om Scal P construction uses the tens apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean#L73-L81
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean#L73-L81

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.tens_apply {n : ℕ} (X : GMod n) (χ : Fin n → ℂ) (hS : ScalChar X χ) (u : ℂ) (w : Fin n → X.V) :
    qdet (tensE X) u (u • w + om X w) =
      Formalism.QuantumDeterminants.capP χ (u - cn n) • ((u + 1) • w + om X w) := by sorry
