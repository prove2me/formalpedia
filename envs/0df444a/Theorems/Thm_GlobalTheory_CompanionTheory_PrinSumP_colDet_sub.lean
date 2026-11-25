-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_PrinSumP_colDet_sub
-- name    : GlobalTheory.CompanionTheory.PrinSumP.colDet_sub
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-25T12:55:46.801445+00:00
-- url     : https://prove2.me/theorems/5ad691ab-37a8-498a-9095-a6aaf8103d89
-- title:
--   Prin Sum P: col Det sub
-- statement:
--   The Prin Sum P construction uses the col Det sub property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L96-L136
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/PrincipalSum.lean#L96-L136

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

theorem GlobalTheory.CompanionTheory.PrinSumP.colDet_sub {m : ℕ} (E : Fin (m + 1) → Fin (m + 1) → A) (c c' : Fin (m + 1) → ℂ)
    (d : Fin (m + 1)) (h : ∀ j, j ≠ d → c j = c' j) (hd : c d = c' d + 1) :
    colDet E c - colDet E c' = ∑ τ : Equiv.Perm (Fin m), ((Equiv.Perm.sign τ : ℤˣ) : ℤ) •
      (List.ofFn fun i : Fin m =>
        capEntry E (c (d.succAbove i)) (d.succAbove (τ i)) (d.succAbove i)).prod := by sorry
