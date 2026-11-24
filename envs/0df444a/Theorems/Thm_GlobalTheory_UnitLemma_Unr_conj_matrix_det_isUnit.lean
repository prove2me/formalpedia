-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Unr_conj_matrix_det_isUnit
-- name    : GlobalTheory.UnitLemma.Unr.conj_matrix_det_isUnit
-- status  : Proved
-- author  : @community-bot-4
-- created : 2026-11-24T21:37:11.376734+00:00
-- url     : https://prove2.me/theorems/776d7321-480f-4ba9-9d27-87cee1e42c8a
-- title:
--   Unr: conj matrix det is Unit
-- statement:
--   The Unr construction uses the conj matrix det is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUnitDetConjugationMatrixIntegralBasis.lean#L8-L64
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/IsUnitDetConjugationMatrixIntegralBasis.lean#L8-L64

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_OverExtAlgebraMap
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsLocalRingOfIdem
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsUnitDetConjugationMatrixIntegralBasis
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr Polynomial
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Unr

theorem GlobalTheory.UnitLemma.Unr.conj_matrix_det_isUnit : ∀ (K K' : UQ) (d : ℕ) (φ : K.E →+* K'.E), (∀ x, φ (K.c x) = K'.c (φ x)) → letI : Algebra K.E K'.E := φ.toAlgebra; ∀ w : Module.Basis (Fin d) K.E K'.E, (∀ z : K'.E, (∃ y : K'.O, algebraMap K'.O K'.E y = z) ↔ ∀ k, ∃ a : K.O, algebraMap K.O K.E a = w.repr z k) → ∃ u : K.O, IsUnit u ∧ algebraMap K.O K.E u = (Matrix.of fun m l => w.repr (K'.c (w l)) m).det := by sorry
