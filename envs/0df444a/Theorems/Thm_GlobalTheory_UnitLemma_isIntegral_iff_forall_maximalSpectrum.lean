-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_isIntegral_iff_forall_maximalSpectrum
-- name    : GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T21:37:59.518369+00:00
-- url     : https://prove2.me/theorems/99f24e6d-7574-4e23-8afd-8d500443aecc
-- title:
--   Unit Lemma: is Integral iff forall maximal Spectrum
-- statement:
--   The Unit Lemma construction uses the is Integral iff forall maximal Spectrum property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralIffForallMaximalSpectrumResidue.lean#L8-L41
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsIntegralIffForallMaximalSpectrumResidue.lean#L8-L41

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsIntegralIffForallMaximalSpectrumResidue
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
open GlobalTheory GlobalTheory.UnitLemma

theorem GlobalTheory.UnitLemma.isIntegral_iff_forall_maximalSpectrum (K : UQ) (B : InvAlg K) (hred : IsReduced B.A) (x : B.A) :
    IsIntegral K.O x ↔ ∀ m : MaximalSpectrum B.A, IsIntegral K.O (Ideal.Quotient.mk m.asIdeal x) := by sorry
