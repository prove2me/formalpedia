-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgHeckeBack_eeVd_apply
-- name    : GlobalTheory.CompanionTheory.RgHeckeBack.eeVd_apply
-- status  : Proved
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:34.206809+00:00
-- url     : https://prove2.me/theorems/d2ab4c61-d4c7-5b67-8bbc-8f9ac2763030
-- title:
--   Rg Hecke Back: ee Vd apply
-- statement:
--   The Rg Hecke Back construction uses the ee Vd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeBackwardStable.lean#L19-L21
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeBackwardStable.lean#L19-L21

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

theorem GlobalTheory.CompanionTheory.RgHeckeBack.eeVd_apply (X : GMod n) (f : Fin n → X.V) (a : Fin n) :
    eeVd X.E f a = -∑ c, X.E a c (f c) := by sorry
