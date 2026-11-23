-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_mul_eq_zero_of_idem
-- name    : GlobalTheory.UnitLemma.Desc.mul_eq_zero_of_idem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:12.329808+00:00
-- url     : https://prove2.me/theorems/60366b64-a1a9-413f-aba4-923c2524be1b
-- title:
--   Desc: mul eq zero of idem
-- statement:
--   The Desc construction uses the mul eq zero of idem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartFrameProperties.lean#L123-L125
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartFrameProperties.lean#L123-L125

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

theorem GlobalTheory.UnitLemma.Desc.mul_eq_zero_of_idem {e : ι → B.A} (he : OrthogonalIdempotents e) {i j : ι} (hij : i ≠ j) {a b : B.A}
    (ha : a * e i = a) (hb : b * e j = b) : a * b = 0 := by sorry
