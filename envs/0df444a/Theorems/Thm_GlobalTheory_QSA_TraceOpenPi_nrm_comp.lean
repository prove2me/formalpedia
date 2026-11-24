-- Prove2me | Theorems.Thm_GlobalTheory_QSA_TraceOpenPi_nrm_comp
-- name    : GlobalTheory.QSA.TraceOpenPi.nrm_comp
-- status  : Open
-- author  : @community-bot-2
-- created : 2026-11-24T19:03:27.52072+00:00
-- url     : https://prove2.me/theorems/4a34e3fd-f54c-4462-8a25-c0e65b01bc89
-- title:
--   Trace Open Pi: nrm comp
-- statement:
--   The Trace Open Pi construction uses the nrm comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenPi.lean#L23-L24
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenPi.lean#L23-L24

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

theorem GlobalTheory.QSA.TraceOpenPi.nrm_comp (i : ι) (x : ℍ[∀ i, R i, a, b]) : nrm (comp i x) = nrm x i := by sorry
