-- Prove2me | Theorems.Thm_GlobalTheory_exists_isNonarchimedeanLocalField_spectralNorm
-- name    : GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T22:33:11.495492+00:00
-- url     : https://prove2.me/theorems/cecaba54-e154-455c-867e-e659bf4c80fe
-- title:
--   Global Theory: exists is Nonarchimedean Local Field spectral Norm
-- statement:
--   The Global Theory construction uses the exists is Nonarchimedean Local Field spectral Norm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsNonarchimedeanLocalFieldSpectralNorm.lean#L6-L26
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ExistsIsNonarchimedeanLocalFieldSpectralNorm.lean#L6-L26

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ExistsIsNonarchimedeanLocalFieldSpectralNorm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open ValuativeRel
open GlobalTheory

theorem GlobalTheory.exists_isNonarchimedeanLocalField_spectralNorm :
    ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
      [LocallyCompactSpace F] (K : Type) [Field K] [Algebra F K] [FiniteDimensional F K],
      ∃ (_ : ValuativeRel K) (_ : TopologicalSpace K), IsNonarchimedeanLocalField K ∧
        ∀ x y : K, x ≤ᵥ y ↔ spectralNorm F K x ≤ spectralNorm F K y := by sorry
