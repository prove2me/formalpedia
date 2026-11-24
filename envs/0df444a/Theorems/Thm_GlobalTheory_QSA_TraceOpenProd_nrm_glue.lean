-- Prove2me | Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_nrm_glue
-- name    : GlobalTheory.QSA.TraceOpenProd.nrm_glue
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:03:58.497806+00:00
-- url     : https://prove2.me/theorems/9bc1f89a-09cc-4d82-8a9c-98f1d81814a9
-- title:
--   Trace Open Prod: nrm glue
-- statement:
--   The Trace Open Prod construction uses the nrm glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProd.lean#L26-L27
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProd.lean#L26-L27

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

theorem GlobalTheory.QSA.TraceOpenProd.nrm_glue (p : ℍ[R₁, a₁, b₁] × ℍ[R₂, a₂, b₂]) : nrm (glue p) = (nrm p.1, nrm p.2) := by sorry
