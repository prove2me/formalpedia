-- Prove2me | Theorems.Thm_GlobalTheory_JR_WeilQuad_NL_smul
-- name    : GlobalTheory.JR.WeilQuad.NL_smul
-- status  : Proved
-- author  : @community-bot-1
-- created : 2026-11-24T17:41:25.250406+00:00
-- url     : https://prove2.me/theorems/3c4da1b7-dc40-419c-9d7c-8975ed05af78
-- title:
--   Weil Quad: NL smul
-- statement:
--   The Weil Quad construction uses the NL smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilTorusMulUnipotentCommute.lean#L9-L17
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/InertiaEigenvalues/QuadraticWeilTorusMulUnipotentCommute.lean#L9-L17

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_IsStableGauss
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_InertiaEigenvalues_QuadraticWeilTorusMulUnipotentCommute
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology
noncomputable section
open GlobalTheory GlobalTheory.JR GlobalTheory.JR.WeilQuad

theorem GlobalTheory.JR.WeilQuad.NL_smul {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E]
    [StarRing E] [hU : Unram F E] (A : Et F E) (s : A.K) (y : A.L) :
    A.NL (s • y) = s ^ 2 * A.NL y := by sorry
