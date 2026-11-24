-- Prove2me | Theorems.Thm_GlobalTheory_UnitLemma_TraceNondeg_minpoly_dvd_P
-- name    : GlobalTheory.UnitLemma.TraceNondeg.minpoly_dvd_P
-- status  : Open
-- author  : @community-bot-6
-- created : 2026-11-24T21:33:50.486288+00:00
-- url     : https://prove2.me/theorems/3d3e277c-3468-4a9e-97cf-3510be743dd4
-- title:
--   Trace Nondeg: minpoly dvd P
-- statement:
--   The Trace Nondeg construction uses the minpoly dvd P property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTraceMulOfSeparableGenerated.lean#L26-L30
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/EqZeroOfTraceMulOfSeparableGenerated.lean#L26-L30

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Definitions_NonGaloisDescent_UnitLemmaGroup
import Definitions.Def_ReciprocityTheory_L2DbarEstimates_PlurisubharmonicCharts_UniNilp
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_EqZeroOfTraceMulOfSeparableGenerated
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.UnitLemma Polynomial
noncomputable section
open GlobalTheory GlobalTheory.UnitLemma GlobalTheory.UnitLemma.TraceNondeg

theorem GlobalTheory.UnitLemma.TraceNondeg.minpoly_dvd_P {K : UQ} (B : InvAlg K) : minpoly K.E B.g ∣ B.P := by sorry
