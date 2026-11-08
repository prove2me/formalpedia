-- Prove2me | Theorems.Thm_LocalLog_isOpen_goodDomain
-- name    : LocalLog.isOpen_goodDomain
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:40:23.903625+00:00
-- url     : https://prove2.me/theorems/c7729c6e-7e7b-4c46-8632-4393e98a204a
-- title:
--   LeanLevy: LocalLog.isOpen_goodDomain
-- statement:
--   Source-header theorem from the pinned LeanLevy library. The source section parameters are made explicit. Its original proof has not been transplanted or verified.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L88

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

theorem LocalLog.isOpen_goodDomain (hφ_cont : Continuous φ) :
    IsOpen (LocalLog.goodDomain φ) := by sorry
