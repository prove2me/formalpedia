-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_core
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.core
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:21.592063+00:00
-- url     : https://prove2.me/theorems/907d14b6-de98-51f0-929e-7fd3b619c51c
-- title:
--   Step Char Pf: core
-- statement:
--   The Step Char Pf construction uses the core property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L134-L176
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L134-L176

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
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.core {D c ν : A} {k M : ℕ} {w r : ℂ} (hw : w ≠ 0) (hν : ν ^ M = 0)
    (hN : (c - algebraMap ℂ A (r * w)) ^ k = 0) (hcν : Commute c ν) (hDν : Commute D ν)
    (hid : D * (algebraMap ℂ A w + ν) = c * (algebraMap ℂ A (w + 1) + ν)) :
    (D - algebraMap ℂ A (r * (w + 1))) ^ (k + M) = 0 := by sorry
