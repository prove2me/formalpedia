-- Prove2me | Theorems.Thm_GlobalTheory_CompanionTheory_RgExhHecke_NonScalProof_om_nnPlus
-- name    : GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.om_nnPlus
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-25T12:48:16.707886+00:00
-- url     : https://prove2.me/theorems/a453501f-6027-5799-a9cd-824e30dfc255
-- title:
--   Non Scal Proof: om nn Plus
-- statement:
--   The Non Scal Proof construction uses the om nn Plus property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeNonScalar.lean#L104-L138
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/CompanionTheory/SpectralGeometry/LocalGlobalProofs/StableLattices/HeckeNonScalar.lean#L104-L138

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

theorem GlobalTheory.CompanionTheory.RgExhHecke.NonScalProof.om_nnPlus {m : ℕ} (X : GMod (m + 1)) (y : Fin (m + 1) → ℂ) (x : ℂ) (v : X.V) :
    om X (nnPlus X.E y x v) + x • nnPlus X.E y x v = fun b => y b • capelliC X.E x v := by sorry
