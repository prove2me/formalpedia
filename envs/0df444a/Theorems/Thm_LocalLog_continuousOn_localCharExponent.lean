-- Prove2me | Theorems.Thm_LocalLog_continuousOn_localCharExponent
-- name    : LocalLog.continuousOn_localCharExponent
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:41:48.144676+00:00
-- url     : https://prove2.me/theorems/764354d9-d96e-43dd-b417-c875ee59168f
-- title:
--   LeanLevy: LocalLog.continuousOn_localCharExponent
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L96

import Init
import Mathlib.Topology.Defs.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Module.Connected
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
open Topology
universe v
section
variable {E : Sort (v + 1)} [TopologicalSpace E] [Zero E] {φ : E → ℂ}

theorem LocalLog.continuousOn_localCharExponent (hφ_cont : Continuous φ) :
    ContinuousOn (LocalLog.localCharExponent φ) (LocalLog.goodDomain φ) := by sorry
