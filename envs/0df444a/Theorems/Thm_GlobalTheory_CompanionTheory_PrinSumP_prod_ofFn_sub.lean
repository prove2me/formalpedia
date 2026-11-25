-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_prod_ofFn_sub
-- name    : GlobalTheory.CompanionTheory.PrinSumP.prod_ofFn_sub
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:50:19.546069+00:00
-- url     : https://prove2.me/theorems/b382ee58-f1d8-478f-92fc-8ee2e1f72879
-- title:
--   Prin Sum P: prod of Fn sub
-- statement:
--   The Prin Sum P construction uses the prod of Fn sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L15-L42
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L15-L42

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

theorem GlobalTheory.CompanionTheory.PrinSumP.prod_ofFn_sub : ∀ (m : ℕ) (f g : Fin (m + 1) → A) (d : Fin (m + 1)),
    (∀ j, j ≠ d → f j = g j) → f d = g d + 1 →
    (List.ofFn f).prod - (List.ofFn g).prod = (List.ofFn (f ∘ d.succAbove)).prod := by sorry
