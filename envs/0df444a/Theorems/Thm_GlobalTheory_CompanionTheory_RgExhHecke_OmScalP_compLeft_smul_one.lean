-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_OmScalP_compLeft_smul_one
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.compLeft_smul_one
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-25T14:29:52.595397+00:00
-- url     : https://prove2.me/theorems/f73a098b-a63b-4d49-a581-741a1cad4819
-- title:
--   Om Scal P: comp Left smul one
-- statement:
--   The Om Scal P construction uses the comp Left smul one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean#L68-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaScalar.lean#L68-L71

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.OmScalP.compLeft_smul_one {V : Type} [AddCommGroup V] [Module ℂ V] {n : ℕ} (c : ℂ) (w : Fin n → V) :
    (c • (1 : Module.End ℂ V)).compLeft (Fin n) w = c • w := by sorry
