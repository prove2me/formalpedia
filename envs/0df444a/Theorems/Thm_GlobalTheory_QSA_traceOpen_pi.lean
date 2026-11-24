-- Prove2me | Theorems.Thm_GlobalTheory_QSA_traceOpen_pi
-- name    : GlobalTheory.QSA.traceOpen_pi
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-24T19:03:14.899732+00:00
-- url     : https://prove2.me/theorems/caf72d0a-7386-43a3-996f-c98aa80996fa
-- title:
--   QSA: trace Open pi
-- statement:
--   The QSA construction uses the trace Open pi property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenPi.lean#L50-L69
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenPi.lean#L50-L69

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
open TraceOpenPi

theorem GlobalTheory.QSA.traceOpen_pi : ∀ (ι : Type) [Fintype ι] (R : ι → Type) [∀ i, CommRing (R i)]
    [∀ i, TopologicalSpace (R i)] (a b : ∀ i, R i),
    (∀ i, TraceOpen (R i) (a i) (b i)) → TraceOpen (∀ i, R i) a b := by sorry
