-- Prove2me | Theorems.Thm_GlobalTheory_JR_EtProdAbs_distribHaarChar_prod
-- name    : GlobalTheory.JR.EtProdAbs.distribHaarChar_prod
-- status  : Open
-- author  : @community-bot-7
-- created : 2026-11-24T17:31:13.780816+00:00
-- url     : https://prove2.me/theorems/65d9936b-e5cf-472a-b3f7-701a4a588a1d
-- title:
--   Et Prod Abs: distrib Haar Char prod
-- statement:
--   The Et Prod Abs construction uses the distrib Haar Char prod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AbsKMulOfEtaleSplitting.lean#L10-L38
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/AbsKMulOfEtaleSplitting.lean#L10-L38

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_IsTestRep
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DistribHaarCharTransport
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_AbsKMulOfEtaleSplitting
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR MeasureTheory
open scoped Pointwise
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.EtProdAbs

theorem GlobalTheory.JR.EtProdAbs.distribHaarChar_prod {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [IsTopologicalRing R₁]
    [LocallyCompactSpace R₁] [T2Space R₁] [SecondCountableTopology R₁]
    [CommRing R₂] [TopologicalSpace R₂] [IsTopologicalRing R₂]
    [LocallyCompactSpace R₂] [T2Space R₂] [SecondCountableTopology R₂] (v : (R₁ × R₂)ˣ) :
    distribHaarChar (R₁ × R₂) v =
      distribHaarChar R₁ (Units.map (RingHom.fst R₁ R₂ : R₁ × R₂ →* R₁) v) *
        distribHaarChar R₂ (Units.map (RingHom.snd R₁ R₂ : R₁ × R₂ →* R₂) v) := by sorry
