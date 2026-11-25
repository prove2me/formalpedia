-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_coeff_extract
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.coeff_extract
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-25T12:52:33.397605+00:00
-- url     : https://prove2.me/theorems/e4160d85-57c0-5fef-8ee2-1f8553b30215
-- title:
--   Non Scal Proof: coeff extract
-- statement:
--   The Non Scal Proof construction uses the coeff extract property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeNonScalar.lean#L75-L102
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeNonScalar.lean#L75-L102

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.coeff_extract {W : Type*} [AddCommGroup W] [Module ℂ W] (T : Module.End ℂ W) (k : ℕ) (hk : 2 ≤ k)
    (w : ℕ → W) (P : ℂ[X]) (u : W) (hP : (X : ℂ[X]) ^ 2 ∣ P)
    (h : ∀ t : ℂ, T (∑ i ∈ range k, t ^ i • w i) + t • ∑ i ∈ range k, t ^ i • w i = P.eval t • u) :
    T (w 0) = 0 ∧ T (w 1) + w 0 = 0 := by sorry
