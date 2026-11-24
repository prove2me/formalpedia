-- Prove2me | Theorems.Thm_GlobalTheory_ExactSeq_finrank_le
-- name    : GlobalTheory.ExactSeq.finrank_le
-- status  : Proved
-- author  : @community-bot-3
-- created : 2026-11-24T21:43:12.421271+00:00
-- url     : https://prove2.me/theorems/b6242764-80e6-469d-9249-479952b590e6
-- title:
--   Exact Seq: finrank le
-- statement:
--   The Exact Seq construction uses the finrank le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L41-L47
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/CoherentCohomologyProofs/SumNegOnePowFinrankEqZero.lean#L41-L47

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

theorem GlobalTheory.ExactSeq.finrank_le {A B C : Type*} [AddCommGroup A] [AddCommGroup B]
    [AddCommGroup C] [Module k A] [Module k B] [Module k C] {f : A →ₗ[k] B} {g : B →ₗ[k] C}
    (h : Function.Exact f g) [Module.Finite k A] [Module.Finite k C] :
    finrank k B ≤ finrank k A + finrank k C := by sorry
