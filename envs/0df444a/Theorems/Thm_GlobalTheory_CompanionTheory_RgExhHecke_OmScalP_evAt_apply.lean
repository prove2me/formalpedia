-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_OmScalP_evAt_apply
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.evAt_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T14:32:43.700043+00:00
-- url     : https://prove2.me/theorems/3680ce0f-91f9-42fd-a61b-3db4de1728bb
-- title:
--   Om Scal P: ev At apply
-- statement:
--   The Om Scal P construction uses the ev At apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean#L22-L22
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean#L22-L22

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.evAt_apply (u : ℂ) (p : A[X]) : evAt u p = eval₂ (RingHom.id A) (algebraMap ℂ A u) p := by sorry
