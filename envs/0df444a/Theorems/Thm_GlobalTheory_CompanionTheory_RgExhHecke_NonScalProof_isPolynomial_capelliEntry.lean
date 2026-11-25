-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_isPolynomial_capelliEntry
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.isPolynomial_capelliEntry
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T12:48:07.33329+00:00
-- url     : https://prove2.me/theorems/8d975c88-b9b8-5bf2-a77b-988447bd088b
-- title:
--   Non Scal Proof: is Polynomial capelli Entry
-- statement:
--   The Non Scal Proof construction uses the is Polynomial capelli Entry property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeNonScalar.lean#L46-L54
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeNonScalar.lean#L46-L54

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.isPolynomial_capelliEntry {n : ℕ} (E : Fin n → Fin n → A) (x₀ : ℂ) (a b : Fin n) :
    IsP (fun t : ℂ => capEntry E (x₀ + t) a b) := by sorry
