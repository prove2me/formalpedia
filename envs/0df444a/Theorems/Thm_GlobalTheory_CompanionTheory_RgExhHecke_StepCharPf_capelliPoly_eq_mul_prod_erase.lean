-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_capelliPoly_eq_mul_prod_erase
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.capelliPoly_eq_mul_prod_erase
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T15:17:22.258951+00:00
-- url     : https://prove2.me/theorems/379f6ff6-d40c-4895-b616-b223058ef754
-- title:
--   Step Char Pf: capelli Poly eq mul prod erase
-- statement:
--   The Step Char Pf construction uses the capelli Poly eq mul prod erase property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L343-L346
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L343-L346

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.capelliPoly_eq_mul_prod_erase (χ : Fin n → ℂ) (s : Fin n) (Y : ℂ) :
    capP χ Y = (∏ t ∈ univ.erase s, (Y + χ t)) * (Y + χ s) := by sorry
