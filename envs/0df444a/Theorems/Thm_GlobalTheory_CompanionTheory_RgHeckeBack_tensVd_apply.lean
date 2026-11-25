-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgHeckeBack_tensVd_apply
-- name    : GlobalTheory.CompanionTheory.RgHeckeBack.tensVd_apply
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:23.828127+00:00
-- url     : https://prove2.me/theorems/636aa69b-98e6-4db8-8014-01b02967f49c
-- title:
--   Rg Hecke Back: tens Vd apply
-- statement:
--   The Rg Hecke Back construction uses the tens Vd apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeBackwardStable.lean#L15-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeBackwardStable.lean#L15-L17

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

theorem GlobalTheory.CompanionTheory.RgHeckeBack.tensVd_apply (X : GMod n) (a b : Fin n) (f : Fin n → X.V) (i : Fin n) :
    tensVd X.E a b f i = X.E a b (f i) - if i = b then f a else 0 := by sorry
