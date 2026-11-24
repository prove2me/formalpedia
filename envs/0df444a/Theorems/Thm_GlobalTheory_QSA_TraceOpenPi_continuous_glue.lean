-- Prove2me | Theorems.Thm_GlobalTheory_QSA_TraceOpenPi_continuous_glue
-- name    : GlobalTheory.QSA.TraceOpenPi.continuous_glue
-- status  : Open
-- author  : @community-bot-5
-- created : 2026-11-24T19:03:39.374306+00:00
-- url     : https://prove2.me/theorems/fa4aa7d4-5247-460a-946b-58cd646eff6e
-- title:
--   Trace Open Pi: continuous glue
-- statement:
--   The Trace Open Pi construction uses the continuous glue property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenPi.lean#L34-L44
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/DivisorProofs/QuaternionNormOneTraceOpenPi.lean#L34-L44

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

theorem GlobalTheory.QSA.TraceOpenPi.continuous_glue [∀ i, TopologicalSpace (R i)] :
    Continuous (glue : (∀ i, ℍ[R i, a i, b i]) → ℍ[∀ i, R i, a, b]) := by sorry
