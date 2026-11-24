-- Prove2me | Theorems.Thm_GlobalTheory_ExactSeq_finite_of_isNoetherian
-- name    : GlobalTheory.ExactSeq.finite_of_isNoetherian
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:41:35.237488+00:00
-- url     : https://prove2.me/theorems/82d78dff-c08d-46e2-8d02-13febdc19433
-- title:
--   Exact Seq: finite of is Noetherian
-- statement:
--   The Exact Seq construction uses the finite of is Noetherian property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L20-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L20-L23

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_QuasicoherentCohomology_HdimEqZeroOfSubsingleton
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_MapFOneInjectiveOfSectionsSurjective
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_CoherentCohomologyProofs_SumNegOnePowFinrankEqZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite Limits Module
universe t v u
noncomputable section
open GlobalTheory
open GlobalTheory.ExactSeq
variable {R : Type*} [Ring R] {A B C : Type*} [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
  [Module R A] [Module R B] [Module R C] {f : A →ₗ[R] B} {g : B →ₗ[R] C}

theorem GlobalTheory.ExactSeq.finite_of_isNoetherian (h : Function.Exact f g) [Module.Finite R A] [IsNoetherian R C] :
    Module.Finite R B := by sorry
