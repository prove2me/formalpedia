-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_norm_ne_zero_of_isUnit
-- name    : GlobalTheory.UnitLemma.Desc.norm_ne_zero_of_isUnit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T21:03:09.379903+00:00
-- url     : https://prove2.me/theorems/fbd5dd2f-3b4d-487b-a126-39ae1718cb1c
-- title:
--   Desc: norm ne zero of is Unit
-- statement:
--   The Desc construction uses the norm ne zero of is Unit property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartFrameProperties.lean#L22-L23
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartFrameProperties.lean#L22-L23

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

theorem GlobalTheory.UnitLemma.Desc.norm_ne_zero_of_isUnit {u : B.A} (hu : IsUnit u) : Algebra.norm K.E u ≠ 0 := by sorry
