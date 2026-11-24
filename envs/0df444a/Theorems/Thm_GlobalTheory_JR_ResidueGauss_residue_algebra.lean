-- Prove2me | Theorems.Thm_GlobalTheory_JR_ResidueGauss_residue_algebra
-- name    : GlobalTheory.JR.ResidueGauss.residue_algebra
-- status  : Open
-- author  : @community-bot-8
-- created : 2026-11-24T17:36:08.416831+00:00
-- url     : https://prove2.me/theorems/12847fce-ca88-4ac2-949d-e3eb713a94f4
-- title:
--   Residue Gauss: residue algebra
-- statement:
--   The Residue Gauss construction uses the residue algebra property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidueGaussIntegralNormForm.lean#L105-L157
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/ResidueGaussIntegralNormForm.lean#L105-L157

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NonemptyMeasAndReps
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedStandardAddCharConductorProperties
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_ResidueGaussIntegralNormForm
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open scoped Pointwise
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.ResidueGauss

theorem GlobalTheory.JR.ResidueGauss.residue_algebra {K L : Type} [CommRing K] [CommRing L] [StarRing L] [Algebra K L]
    (hK : IsField K) (hinj : Function.Injective (algebraMap K L)) (N : L → K)
    (hN : ∀ y, algebraMap K L (N y) = y * star y) (O : Subring L) (ϖ : Kˣ)
    (hOs : ∀ y ∈ O, star y ∈ O) (hϖO : algebraMap K L (ϖ : K) ∈ O)
    (hϖnu : ¬ ∃ z ∈ O, algebraMap K L (ϖ : K) * z = 1)
    (hdich : ∀ y ∈ O, (∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) ∨ ∃ z ∈ O, y * z = 1)
    (hnorm : ∀ s : K, algebraMap K L s ∈ O → (∃ r ∈ O, algebraMap K L s * r = 1) → ∃ w ∈ O, N w = s) :
    (∀ y ∈ O, (¬ ∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) →
      algebraMap K L (N y) ∈ O ∧ (¬ ∃ t, algebraMap K L t ∈ O ∧ N y = ϖ * t) ∧
        ∃ r, algebraMap K L r ∈ O ∧ N y * r = 1) ∧
    (∀ s, algebraMap K L s ∈ O → (¬ ∃ t, algebraMap K L t ∈ O ∧ s = ϖ * t) →
      (∃ r, algebraMap K L r ∈ O ∧ s * r = 1) ∧ ∃ w ∈ O, ∃ v ∈ O, w * v = 1 ∧ N w = s) := by sorry
