-- Prove2me | Theorems.Thm_GlobalTheory_QSA_TraceOpenProd_glue_fst_snd
-- name    : GlobalTheory.QSA.TraceOpenProd.glue_fst_snd
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:03:33.44395+00:00
-- url     : https://prove2.me/theorems/4f30b0bb-78b7-45cf-8151-7bf12b8a110a
-- title:
--   Trace Open Prod: glue fst snd
-- statement:
--   The Trace Open Prod construction uses the glue fst snd property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProd.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenProd.lean#L23-L24

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

theorem GlobalTheory.QSA.TraceOpenProd.glue_fst_snd (x : ℍ[R₁ × R₂, (a₁, a₂), (b₁, b₂)]) : glue (fst x, snd x) = x := by sorry
