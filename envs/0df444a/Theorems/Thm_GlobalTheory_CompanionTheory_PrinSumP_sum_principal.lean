-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_sum_principal
-- name    : GlobalTheory.CompanionTheory.PrinSumP.sum_principal
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-25T12:50:59.592688+00:00
-- url     : https://prove2.me/theorems/f060d520-28e6-5d4f-83ff-99be6f8d146e
-- title:
--   Prin Sum P: sum principal
-- statement:
--   The Prin Sum P construction uses the sum principal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L172-L184
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L172-L184

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

theorem GlobalTheory.CompanionTheory.PrinSumP.sum_principal {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (x : ℂ) :
    ∑ d : Fin (m + 1), cminor E d.succAbove d.succAbove (x - 1) = qdet E x - qdet E (x - 1) := by sorry
