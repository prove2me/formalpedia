-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_IsP_sum
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.IsP.sum
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:17.30647+00:00
-- url     : https://prove2.me/theorems/2aa346bf-59ce-5448-a166-e86044072f3b
-- title:
--   Is P: sum
-- statement:
--   The Is P construction uses the sum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeNonScalar.lean#L33-L36
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeNonScalar.lean#L33-L36

import Mathlib
import Definitions.Def_CompanionTheory_RealGroups_DiscreteSeries_DiscreteSeriesClassification_DiscreteSeriesExhaustion_HeckeAlgebraActions_BackStable
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_QuantumDeterminantEquality
import Definitions.Def_CompanionTheory_SpectralGeometry_LocalGlobalProofs_StableLattices_HeckeNonScalar
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Polynomial
open GlobalTheory GlobalTheory.CompanionTheory GlobalTheory.CompanionTheory.RgExhHecke GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof
open CompanionTheory.RgExh CompanionTheory.RgExh.Hk ReciprocityTheory.ChartRestriction.DS.Lap.Capelli
variable {A : Type*} [Ring A] [Algebra ℂ A]

theorem GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.IsP.sum {ι : Type*} (s : Finset ι) {f : ι → ℂ → A} (hf : ∀ i, IsP (f i)) :
    IsP (fun t => ∑ i ∈ s, f i t) := by sorry
