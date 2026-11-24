-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_NearZero_finite_K_L
-- name    : GlobalTheory.JR.WeilQuad.NearZero.finite_K_L
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-23T20:53:05.964391+00:00
-- url     : https://prove2.me/theorems/d1130c8e-7edb-4eb7-a47c-cd02d23f10c9
-- title:
--   Near Zero: finite K L
-- statement:
--   The Near Zero construction uses the finite K L property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaleTraceAddCharNormEqOneNearZero.lean#L18-L20
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EtaleTraceAddCharNormEqOneNearZero.lean#L18-L20

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

theorem GlobalTheory.JR.WeilQuad.NearZero.finite_K_L [Unram F E] (A : Et F E) : Module.Finite A.K A.L := by sorry
