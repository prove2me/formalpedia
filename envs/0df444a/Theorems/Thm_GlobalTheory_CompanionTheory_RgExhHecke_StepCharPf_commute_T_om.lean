-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_commute_T_om
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.commute_T_om
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:52.274369+00:00
-- url     : https://prove2.me/theorems/e22f699f-2f45-4339-9b56-d6dd405f1f7e
-- title:
--   Step Char Pf: commute T om
-- statement:
--   The Step Char Pf construction uses the commute T om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L372-L373
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L372-L373

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.commute_T_om (X : GMod n) (u : ℂ) : Commute (qdet (tensE X) u) (om X) := by sorry
