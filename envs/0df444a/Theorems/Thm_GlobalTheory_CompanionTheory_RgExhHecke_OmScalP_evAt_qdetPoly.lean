-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_OmScalP_evAt_qdetPoly
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.evAt_qdetPoly
-- status  : Open
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:07.103731+00:00
-- url     : https://prove2.me/theorems/7e6571c5-518d-5c3a-b1f3-9711ad883aaa
-- title:
--   Om Scal P: ev At qdet Poly
-- statement:
--   The Om Scal P construction uses the ev At qdet Poly property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean#L36-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean#L36-L41

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
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.evAt_qdetPoly {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) : evAt u (qdetPoly E) = qdet E u := by sorry
