-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_NearZero_NL_zero
-- name    : GlobalTheory.JR.WeilQuad.NearZero.NL_zero
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:41:21.37232+00:00
-- url     : https://prove2.me/theorems/3e35b10d-92db-476a-aa9d-e757590f1237
-- title:
--   Near Zero: NL zero
-- statement:
--   The Near Zero construction uses the NL zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaleTraceAddCharNormEqOneNearZero.lean#L36-L40
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaleTraceAddCharNormEqOneNearZero.lean#L36-L40

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EtaleTraceAddCharNormEqOneNearZero
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad GlobalTheory.JR.WeilQuad.NearZero
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]

theorem GlobalTheory.JR.WeilQuad.NearZero.NL_zero [Unram F E] (A : Et F E) (hK : IsField A.K) (hL : IsField A.L) : A.NL (0 : A.L) = 0 := by sorry
