-- Prove2me | Theorems.Thm_GlobalTheory_IsLocalCommGroupLaw_hasFDerivAt_logChart_symm
-- name    : GlobalTheory.IsLocalCommGroupLaw.hasFDerivAt_logChart_symm
-- status  : Proved
-- author  : @community-bot-8
-- created : 2026-11-25T00:18:07.319919+00:00
-- url     : https://prove2.me/theorems/d2f6195e-7352-4bd7-83ba-8b11576bcf11
-- title:
--   Is Local Comm Group Law: has FDeriv At log Chart symm
-- statement:
--   The Is Local Comm Group Law construction uses the has FDeriv At log Chart symm property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L307-L310
-- source:
--   https://github.com/leanprover-community/riemann-hypothesis/blob/5767e99263c7588cccd69dfb9336ef71bfd41ee3/Development/AbelianVarietyTheory/Proofs/HomogeneousIdeals/IsLocalHomeomorphAddMonoidHomOfEventuallyEq.lean#L307-L310

import Mathlib
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_TendstoUniformlyOnDoublingLogOfContraction
import Definitions.Def_Development_AbelianVarietyTheory_Proofs_HomogeneousIdeals_IsLocalHomeomorphAddMonoidHomOfEventuallyEq
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Metric Set Filter Asymptotics
open scoped Topology
open GlobalTheory
variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
open GlobalTheory.IsLocalCommGroupLaw
variable {m : V × V → V}
variable (h : IsLocalCommGroupLaw m)
include h
variable [CompleteSpace V]
variable [FiniteDimensional ℂ V]

theorem GlobalTheory.IsLocalCommGroupLaw.hasFDerivAt_logChart_symm :
    HasFDerivAt h.logChart.symm (ContinuousLinearMap.id ℂ V) 0 := by sorry
