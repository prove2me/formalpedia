-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_nil_pow
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.nil_pow
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:17.708099+00:00
-- url     : https://prove2.me/theorems/f057a045-b7ac-5428-b5f8-f90d39d62dd7
-- title:
--   Step Char Pf: nil pow
-- statement:
--   The Step Char Pf construction uses the nil pow property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L302-L333
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L302-L333

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
variable {V : Type*} [AddCommGroup V] [Module ℂ V]

theorem GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.nil_pow {f : Module.End ℂ V} {a : ℂ} (l : List (Module.End ℂ V))
    (hl : ∀ T ∈ l, ∃ b : ℂ, T = f - b • (1 : Module.End ℂ V)) (K : ℕ) :
    ∀ g ∈ f.maxGenEigenspace a, (l.prod ^ K) g = 0 →
      ((f - a • (1 : Module.End ℂ V)) ^ (l.length * K)) g = 0 := by sorry
