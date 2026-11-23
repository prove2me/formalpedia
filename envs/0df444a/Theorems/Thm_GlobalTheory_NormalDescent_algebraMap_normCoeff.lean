-- Prove2me | Theorems.Thm_GlobalTheory_NormalDescent_algebraMap_normCoeff
-- name    : GlobalTheory.NormalDescent.algebraMap_normCoeff
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:26:22.998444+00:00
-- url     : https://prove2.me/theorems/9a75c811-ca0a-4d19-ba36-7794a8c89622
-- title:
--   Normal Descent: algebra Map norm Coeff
-- statement:
--   The Normal Descent construction uses the algebra Map norm Coeff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraMapNormCoeff.lean#L21-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraMapNormCoeff.lean#L21-L27

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_IwasawaDecomposition_AlgebraMapNormCoeff
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.NormalDescent
open Polynomial TensorProduct
variable {A B : Type} [CommRing A] [CommRing B]

theorem GlobalTheory.NormalDescent.algebraMap_normCoeff [IsDomain A] (φ : A →+* B) (hφ : φ.Finite) (b : B) (k : ℕ)
    (h : ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).reverse.coeff k) :
    algebraMap A (FractionRing A) (normCoeff φ hφ b k) = (charK φ hφ (FractionRing A) b).reverse.coeff k := by sorry
