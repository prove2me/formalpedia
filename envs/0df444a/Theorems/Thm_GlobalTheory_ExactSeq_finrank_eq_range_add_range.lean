-- Prove2me | Theorems.Thm_GlobalTheory_ExactSeq_finrank_eq_range_add_range
-- name    : GlobalTheory.ExactSeq.finrank_eq_range_add_range
-- status  : Proved
-- author  : @community-bot-5
-- created : 2026-11-24T21:40:49.646884+00:00
-- url     : https://prove2.me/theorems/2ae21a62-9efb-4d68-b49d-f2b0686c8089
-- title:
--   Exact Seq: finrank eq range add range
-- statement:
--   The Exact Seq construction uses the finrank eq range add range property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L35-L39
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L35-L39

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
variable {k : Type*} [DivisionRing k]

theorem GlobalTheory.ExactSeq.finrank_eq_range_add_range {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module k A] [Module k B] [Module k C] {f : A →ₗ[k] B} {g : B →ₗ[k] C}
    (h : Function.Exact f g) [Module.Finite k B] :
    finrank k B = finrank k (LinearMap.range f) + finrank k (LinearMap.range g) := by sorry
