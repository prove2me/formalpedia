-- Prove2me | Theorems.Thm_GlobalTheory_NormalDescent_charK_monic
-- name    : GlobalTheory.NormalDescent.charK_monic
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T16:28:37.810233+00:00
-- url     : https://prove2.me/theorems/013406f6-a248-41d2-9b62-d70a83dad944
-- title:
--   Normal Descent: char K monic
-- statement:
--   The Normal Descent construction uses the char K monic property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraMapNormCoeff.lean#L29-L33
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/IwasawaDecomposition/AlgebraMapNormCoeff.lean#L29-L33

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

theorem GlobalTheory.NormalDescent.charK_monic (φ : A →+* B) (hφ : φ.Finite) (K : Type) [Field K] [Algebra A K] (b : B) :
    (charK φ hφ K b).Monic := by sorry
