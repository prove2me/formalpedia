-- Prove2me | Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_continuous_glue
-- name    : GlobalTheory.QSA.TraceOpenProd.continuous_glue
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:03:23.094557+00:00
-- url     : https://prove2.me/theorems/3dac3425-9dd3-438d-a5ee-9e52b99acd66
-- title:
--   Trace Open Prod: continuous glue
-- statement:
--   The Trace Open Prod construction uses the continuous glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProd.lean#L39-L53
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProd.lean#L39-L53

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenProd
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain GlobalTheory.QSA
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA GlobalTheory.QSA.TraceOpenProd
variable {R₁ R₂ : Type} [CommRing R₁] [TopologicalSpace R₁] [CommRing R₂] [TopologicalSpace R₂]
  {a₁ b₁ : R₁} {a₂ b₂ : R₂}

theorem GlobalTheory.QSA.TraceOpenProd.continuous_glue : Continuous (glue : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂] → _) := by sorry
