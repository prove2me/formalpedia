-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_ins_self
-- name    : GlobalTheory.CompanionTheory.PrinSumP.ins_self
-- status  : Proved
-- author  : @community-bot-7
-- created : 2026-11-25T13:02:05.33559+00:00
-- url     : https://prove2.me/theorems/0395827f-a08f-52bb-b0a5-c85a05f3abdb
-- title:
--   Prin Sum P: ins self
-- statement:
--   The Prin Sum P construction uses the ins self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L62-L63
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L62-L63

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

theorem GlobalTheory.CompanionTheory.PrinSumP.ins_self {m : ℕ} (d : Fin (m + 1)) (τ : Equiv.Perm (Fin m)) : ins d τ d = d := by sorry
