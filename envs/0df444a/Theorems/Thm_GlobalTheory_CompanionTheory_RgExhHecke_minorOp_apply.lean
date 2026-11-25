-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_minorOp_apply
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.minorOp_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:48:46.272359+00:00
-- url     : https://prove2.me/theorems/04524639-2b02-5aa8-ad2d-0994cb203195
-- title:
--   Rg Exh Hecke: minor Op apply
-- statement:
--   The Rg Exh Hecke construction uses the minor Op apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L190-L192
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L190-L192

import Mathlib
import Definitions.Def_Formalism_RealPlaceAnalysis_StatementE
import Definitions.Def_ReciprocityTheory_ReductiveGroups_DiscreteSeries_LaplaceOperators_CapelliIdentity_WhittakerZeroStatement
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeRankOne
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Formalism.REAL ReciprocityTheory.ChartRestriction.DS.Lap.Capelli CompanionTheory.RgExh
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.RgExhHecke.minorOp_apply {m : ℕ} (X : GMod (m + 1)) (y : ℂ) (f : Fin (m + 1) → X.V) (a : Fin (m + 1)) :
    minorOp X y f a = ∑ c : Fin (m + 1), ((-1 : ℂ) ^ ((a : ℕ) + (c : ℕ))) • cminor X.E a.succAbove c.succAbove y (f c) := by sorry
