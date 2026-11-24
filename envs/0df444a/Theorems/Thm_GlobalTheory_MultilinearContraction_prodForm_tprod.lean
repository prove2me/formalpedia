-- Prove2me | Theorems.Thm_GlobalTheory_MultilinearContraction_prodForm_tprod
-- name    : GlobalTheory.MultilinearContraction.prodForm_tprod
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T14:43:16.071981+00:00
-- url     : https://prove2.me/theorems/bd62ba45-36fa-457f-963b-c7a91a207608
-- title:
--   Multilinear Contraction: prod Form tprod
-- statement:
--   The Multilinear Contraction construction uses the prod Form tprod property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ContractMultilinearApply.lean#L85-L87
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/ContractMultilinearApply.lean#L85-L87

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_ContractMultilinearApply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open scoped TensorProduct BigOperators
open GlobalTheory GlobalTheory.MultilinearContraction
variable {ι : Type*} [Fintype ι] {R : Type*} [CommSemiring R]
  {X : ι → Type*} [∀ i, AddCommMonoid (X i)] [∀ i, Module R (X i)]

theorem GlobalTheory.MultilinearContraction.prodForm_tprod (φ : ∀ i, X i →ₗ[R] R) (x : ∀ i, X i) :
    prodForm φ (⨂ₜ[R] i, x i) = ∏ i, φ i (x i) := by sorry
