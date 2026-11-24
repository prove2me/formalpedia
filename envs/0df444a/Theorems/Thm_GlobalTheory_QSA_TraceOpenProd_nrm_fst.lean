-- Prove2me | Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_nrm_fst
-- name    : GlobalTheory.QSA.TraceOpenProd.nrm_fst
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:03:56.556287+00:00
-- url     : https://prove2.me/theorems/ed59abed-d2a3-4917-b6f3-a86ae251b8c8
-- title:
--   Trace Open Prod: nrm fst
-- statement:
--   The Trace Open Prod construction uses the nrm fst property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProd.lean#L29-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProd.lean#L29-L30

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

theorem GlobalTheory.QSA.TraceOpenProd.nrm_fst (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : nrm (fst x) = (nrm x).1 := by sorry
