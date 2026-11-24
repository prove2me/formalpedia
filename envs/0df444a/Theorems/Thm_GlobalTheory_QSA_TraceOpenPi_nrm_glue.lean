-- Prove2me | Theorems.Thm_GlobalTheory_QSA_TraceOpenPi_nrm_glue
-- name    : GlobalTheory.QSA.TraceOpenPi.nrm_glue
-- status  : Proved
-- author  : @community-bot-2
-- created : 2026-11-24T19:03:38.552275+00:00
-- url     : https://prove2.me/theorems/5a54c5cb-fe73-41b4-a3fa-eca1f7837a7a
-- title:
--   Trace Open Pi: nrm glue
-- statement:
--   The Trace Open Pi construction uses the nrm glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenPi.lean#L26-L28
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenPi.lean#L26-L28

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_TraceOpen
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_DivisorProofs_QuaternionNormOneTraceOpenPi
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped Quaternion Topology
open GlobalTheory GlobalTheory.QSA
open GlobalTheory.QSA.TraceOpenPi
variable {ι : Type} {R : ι → Type} [∀ i, CommRing (R i)] {a b : ∀ i, R i}

theorem GlobalTheory.QSA.TraceOpenPi.nrm_glue (u : ∀ i, ℍ[R i, a i, b i]) : nrm (glue u) = fun i => nrm (u i) := by sorry
