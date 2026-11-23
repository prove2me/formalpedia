-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_e_mul_eS
-- name    : GlobalTheory.UnitLemma.Desc.e_mul_eS
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:09:34.573163+00:00
-- url     : https://prove2.me/theorems/3e1f7f72-e4c2-4292-98d7-b1aa617e319a
-- title:
--   Desc: e mul e S
-- statement:
--   The Desc construction uses the e mul e S property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartFrameProperties.lean#L40-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartFrameProperties.lean#L40-L44

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

theorem GlobalTheory.UnitLemma.Desc.e_mul_eS {e : ι → B.A} (he : OrthogonalIdempotents e) (i : ι) (I : Finset ι) :
    e i * eS B e I = if i ∈ I then e i else 0 := by sorry
