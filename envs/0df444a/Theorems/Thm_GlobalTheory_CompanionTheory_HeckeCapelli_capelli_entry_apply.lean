-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCapelli_capelli_entry_apply
-- name    : GlobalTheory.CompanionTheory.HeckeCapelli.capelli_entry_apply
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:49:08.336846+00:00
-- url     : https://prove2.me/theorems/31c43570-0b9f-4e67-bf80-d676c7d48d7e
-- title:
--   Hecke Capelli: capelli entry apply
-- statement:
--   The Hecke Capelli construction uses the capelli entry apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaMinor.lean#L12-L15
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaMinor.lean#L12-L15

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEqualityStatement
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_OmegaMinor
import Theorems.Thm_ReciprocityTheory_ChartRestriction_DS_Lap_Capelli_capelliExpand

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.HeckeCapelli
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (cminor capelliC capEntry capelliExpand)

theorem GlobalTheory.CompanionTheory.HeckeCapelli.capelli_entry_apply {n : ℕ} (X : GMod n) (x : ℂ) (d b : Fin n) (v : X.V) :
    capEntry X.E x d b v = X.E d b v + if d = b then x • v else 0 := by sorry
