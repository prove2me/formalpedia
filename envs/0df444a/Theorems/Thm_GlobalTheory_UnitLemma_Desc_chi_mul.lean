-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_Desc_chi_mul
-- name    : GlobalTheory.UnitLemma.Desc.chi_mul
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T21:26:39.001707+00:00
-- url     : https://prove2.me/theorems/dc132cd3-6743-49b0-91b5-fa8f4a5a5ff5
-- title:
--   Desc: chi mul
-- statement:
--   The Desc construction uses the chi mul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartFrameProperties.lean#L62-L67
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/NormCharacterOnIdempotentPartFrameProperties.lean#L62-L67

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

theorem GlobalTheory.UnitLemma.Desc.chi_mul {e : ι → B.A} (he : OrthogonalIdempotents e) (I : Finset ι) {x y : B.A} (hx : IsUnit x)
    (hy : IsUnit y) : chi B e I (x * y) = chi B e I x * chi B e I y := by sorry
