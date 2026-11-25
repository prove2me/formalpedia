-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_capEntry_tensE_apply
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.capEntry_tensE_apply
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:47:14.794246+00:00
-- url     : https://prove2.me/theorems/a4c902da-a684-4f03-8f4b-14cd50722b63
-- title:
--   Rg Exh Hecke: cap Entry tens E apply
-- statement:
--   The Rg Exh Hecke construction uses the cap Entry tens E apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L13-L18
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeRankOne.lean#L13-L18

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.capEntry_tensE_apply (X : GMod n) (x : ℂ) (a b : Fin n) (f : Fin n → X.V) (d : Fin n) :
    capEntry (tensE X) x a b f d = capEntry X.E x a b (f d) + if d = a then f b else 0 := by sorry
