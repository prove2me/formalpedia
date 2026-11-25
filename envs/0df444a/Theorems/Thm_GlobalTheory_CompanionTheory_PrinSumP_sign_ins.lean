-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_sign_ins
-- name    : GlobalTheory.CompanionTheory.PrinSumP.sign_ins
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-25T12:55:20.987705+00:00
-- url     : https://prove2.me/theorems/4cf44ad0-ad7a-4f0b-9745-5cbf9a989683
-- title:
--   Prin Sum P: sign ins
-- statement:
--   The Prin Sum P construction uses the sign ins property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L69-L71
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L69-L71

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

theorem GlobalTheory.CompanionTheory.PrinSumP.sign_ins {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) :
    Equiv.Perm.sign (ins d τ) = Equiv.Perm.sign τ := by sorry
