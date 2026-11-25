-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgHeckeBack_backStable
-- name    : GlobalTheory.CompanionTheory.RgHeckeBack.backStable
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-25T12:48:28.608801+00:00
-- url     : https://prove2.me/theorems/ed8af53b-5d2a-5772-9551-26b897ccc372
-- title:
--   Rg Hecke Back: back Stable
-- statement:
--   The Rg Hecke Back construction uses the back Stable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeBackwardStable.lean#L33-L34
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeBackwardStable.lean#L33-L34

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

theorem GlobalTheory.CompanionTheory.RgHeckeBack.backStable : BackStable := by sorry
