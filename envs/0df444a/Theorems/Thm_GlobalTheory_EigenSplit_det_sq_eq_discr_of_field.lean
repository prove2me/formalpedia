-- Prove2me | Theorems.Thm_GlobalTheory_EigenSplit_det_sq_eq_discr_of_field
-- name    : GlobalTheory.EigenSplit.det_sq_eq_discr_of_field
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T03:52:43.702459+00:00
-- url     : https://prove2.me/theorems/007a9db4-b662-4c6b-8534-fd6c22f3b14b
-- title:
--   Eigen Split: det sq eq discr of field
-- statement:
--   The Eigen Split construction uses the det sq eq discr of field property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L691-L719
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HermitianTraceForms/IsLocallyConstantRankAtStalkEigenSub.lean#L691-L719

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HermitianTraceForms_IsLocallyConstantRankAtStalkEigenSub
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct NumberField
open Polynomial
open GlobalTheory
open GlobalTheory.EigenSplit
variable {E : Type*} [Field E] [NumberField E] {R : Type*} [CommRing R] {ι : Type*} [Fintype ι]
  [DecidableEq ι]

theorem GlobalTheory.EigenSplit.det_sq_eq_discr_of_field {L : Type*} [Field L] {φ : ι → E →+* L}
    (hφ : Function.Injective φ) (b : Module.Basis ι ℤ (𝓞 E)) :
    (Matrix.of fun i j => φ i (b j)).det ^ 2 = (NumberField.discr E : L) := by sorry
