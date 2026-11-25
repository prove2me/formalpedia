-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgHeckeBack_commute_tensVd_eeVd
-- name    : GlobalTheory.CompanionTheory.RgHeckeBack.commute_tensVd_eeVd
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:19.245286+00:00
-- url     : https://prove2.me/theorems/8c242b5c-ada6-4a0c-9db8-a227660aed81
-- title:
--   Rg Hecke Back: commute tens Vd ee Vd
-- statement:
--   The Rg Hecke Back construction uses the commute tens Vd ee Vd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeBackwardStable.lean#L23-L31
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeBackwardStable.lean#L23-L31

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeBackwardStable
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgHeckeBack
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (tensVd eeVd)
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
variable {n : ℕ}

theorem GlobalTheory.CompanionTheory.RgHeckeBack.commute_tensVd_eeVd (X : GMod n) (c d : Fin n) : Commute (tensVd X.E c d) (eeVd X.E) := by sorry
