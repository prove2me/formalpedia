-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_Tm_eq_capEntry
-- name    : GlobalTheory.CompanionTheory.PrinSumP.Tm_eq_capEntry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:50:37.420823+00:00
-- url     : https://prove2.me/theorems/be88c645-279f-4203-b973-a74a164fbdba
-- title:
--   Prin Sum P: Tm eq cap Entry
-- statement:
--   The Prin Sum P construction uses the Tm eq cap Entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L48-L49
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L48-L49

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_PrincipalSum
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
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.PrinSumP
open ReciprocityTheory.ChartRestriction.DS.Lap.Capelli (capEntry cminor)
open Formalism.REAL (Tm qminor qdet)
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem GlobalTheory.CompanionTheory.PrinSumP.Tm_eq_capEntry {n : ℕ} (E : Fin n → Fin n → A) (u : ℂ) (a b : Fin n) :
    Tm E u a b = capEntry E u a b := by sorry
