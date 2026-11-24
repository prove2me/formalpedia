-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_sum_mul_sum_diag
-- name    : GlobalTheory.UnitLemma.Desc.sum_mul_sum_diag
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T21:28:46.139999+00:00
-- url     : https://prove2.me/theorems/0c579660-c54b-4f9d-b92d-62277c5a7f3e
-- title:
--   Desc: sum mul sum diag
-- statement:
--   The Desc construction uses the sum mul sum diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartFrameProperties.lean#L127-L133
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartFrameProperties.lean#L127-L133

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_LinearDescent
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_DltEqZero
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_UnramifiedQuadraticNormsTraceUniformizerFacts
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_NormCharacterOnIdempotentPartFrameProperties
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.Desc
open GlobalTheory.UnitLemma Polynomial Filter Topology
variable {K : UQ} (B : InvAlg K)
variable {ι : Type} [Fintype ι] [DecidableEq ι]

theorem GlobalTheory.UnitLemma.Desc.sum_mul_sum_diag {e : ι → B.A} (he : OrthogonalIdempotents e) (s : Finset ι) (a b : ι → B.A)
    (ha : ∀ i ∈ s, a i * e i = a i) (hb : ∀ i ∈ s, b i * e i = b i) :
    (∑ i ∈ s, a i) * (∑ j ∈ s, b j) = ∑ i ∈ s, a i * b i := by sorry
