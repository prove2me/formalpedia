-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_HeckeCapelli_capelli_component
-- name    : GlobalTheory.CompanionTheory.HeckeCapelli.capelli_component
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T13:42:16.62207+00:00
-- url     : https://prove2.me/theorems/650bc6d2-5156-5c31-b3b6-305cd4a11d0d
-- title:
--   Hecke Capelli: capelli component
-- statement:
--   The Hecke Capelli construction uses the capelli component property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaMinor.lean#L17-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/OmegaMinor.lean#L17-L30

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

theorem GlobalTheory.CompanionTheory.HeckeCapelli.capelli_component {m : ℕ} (X : GMod (m + 1)) (x : ℂ) (f : Fin (m + 1) → X.V) (b : Fin (m + 1)) :
    ∑ c : Fin (m + 1), ∑ d : Fin (m + 1), ((-1 : ℂ) ^ ((d : ℕ) + (c : ℕ))) •
        capEntry X.E x d b (cminor X.E d.succAbove c.succAbove (x - 1) (f c)) = capelliC X.E x (f b) := by sorry
