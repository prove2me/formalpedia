-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_StepCharPf_compLeft_pow_apply
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.compLeft_pow_apply
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T15:17:58.83208+00:00
-- url     : https://prove2.me/theorems/b0012587-c231-4772-9eb6-7e3032f7c8df
-- title:
--   Step Char Pf: comp Left pow apply
-- statement:
--   The Step Char Pf construction uses the comp Left pow apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L356-L364
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/InfinitesimalCharacterStatement.lean#L356-L364

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.StepCharPf.compLeft_pow_apply {V : Type*} [AddCommGroup V] [Module ℂ V] {I : Type*} (T : Module.End ℂ V)
    (c : ℂ) (k : ℕ) (f : I → V) (i : I) :
    ((T.compLeft I - algebraMap ℂ (Module.End ℂ (I → V)) c) ^ k) f i =
      ((T - algebraMap ℂ (Module.End ℂ V) c) ^ k) (f i) := by sorry
