-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExh_commute_compLeft_om
-- name    : GlobalTheory.CompanionTheory.RgExh.commute_compLeft_om
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-25T13:53:46.331706+00:00
-- url     : https://prove2.me/theorems/b9abdb49-e7b0-5263-a163-447908b92191
-- title:
--   Rg Exh: commute comp Left om
-- statement:
--   The Rg Exh construction uses the commute comp Left om property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/QuantumDeterminantTensor.lean#L30-L37
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/QuantumDeterminantTensor.lean#L30-L37

import Mathlib
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaMinorStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOneStatement
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantTensor
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExh
open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk

theorem GlobalTheory.CompanionTheory.RgExh.commute_compLeft_om {n : ℕ} (X : GMod n) (u : ℂ) :
    Commute ((qdet X.E u).compLeft (Fin n)) (om X) := by sorry
