-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_NearZero_finite_E_L
-- name    : GlobalTheory.JR.WeilQuad.NearZero.finite_E_L
-- status  : Open
-- author  : @community-bot-1
-- created : 2026-11-24T17:41:26.810028+00:00
-- url     : https://prove2.me/theorems/ac23a9f8-bf54-4349-a7cc-de072bb800f7
-- title:
--   Near Zero: finite E L
-- statement:
--   The Near Zero construction uses the finite E L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaleTraceAddCharNormEqOneNearZero.lean#L8-L11
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaleTraceAddCharNormEqOneNearZero.lean#L8-L11

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

theorem GlobalTheory.JR.WeilQuad.NearZero.finite_E_L [Unram F E] (A : Et F E) : Module.Finite E A.L := by sorry
