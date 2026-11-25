-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_capelliPoly_add_single
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.capelliPoly_add_single
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:59.521854+00:00
-- url     : https://prove2.me/theorems/98d4523b-771c-4fb6-8e8c-d10c535638b2
-- title:
--   Step Char Pf: capelli Poly add single
-- statement:
--   The Step Char Pf construction uses the capelli Poly add single property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L348-L354
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L348-L354

import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_CayleyHamiltonStatementStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_InfinitesimalCharacterStatement
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf
open _root_.CompanionTheory.RgExh _root_.CompanionTheory.RgExh.Hk
open Formalism.REAL (GlRel qdet qminor Tm)
open Formalism.QuantumDeterminants (capP)
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.capelliPoly_add_single (χ : Fin n → ℂ) (s : Fin n) (Y : ℂ) :
    capP (χ + Pi.single s 1) Y = (∏ t ∈ univ.erase s, (Y + χ t)) * (Y + χ s + 1) := by sorry
