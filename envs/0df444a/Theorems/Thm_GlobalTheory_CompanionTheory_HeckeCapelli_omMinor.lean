-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCapelli_omMinor
-- name    : GlobalTheory.CompanionTheory.HeckeCapelli.omMinor
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:11.379998+00:00
-- url     : https://prove2.me/theorems/162f0fa5-e611-56d1-b226-311519f9ae93
-- title:
--   Hecke Capelli: om Minor
-- statement:
--   The Hecke Capelli construction uses the om Minor property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaMinor.lean#L32-L46
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaMinor.lean#L32-L46

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

theorem GlobalTheory.CompanionTheory.HeckeCapelli.omMinor : OmMinor := by sorry
