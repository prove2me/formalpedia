-- Prove2me | Theorems.Thm_LocalLog_leanlevy_chat29_exists_ball_subset_goodDomain_norm
-- name    : LocalLog.leanlevy_chat29_exists_ball_subset_goodDomain_norm
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T12:52:36.483089+00:00
-- url     : https://prove2.me/theorems/9505b4e0-81bb-4628-9dc8-9b6e111f7755
-- title:
--   Norm-topology neighbourhood of local characteristic exponent domain
-- statement:
--   For a normed additive commutative group, continuity at zero of a complex-valued function taking the value one yields a positive metric ball inside the slit-plane preimage. Corrects the upstream source's unconstrained extra topological-space instance.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L107

import Mathlib.Topology.Defs.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.Analysis.Normed.Module.Connected
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent

open Topology Filter

theorem LocalLog.leanlevy_chat29_exists_ball_subset_goodDomain_norm
    {E : Type*} [SeminormedAddCommGroup E] {φ : E → ℂ}
    (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    ∃ ε > 0, Metric.ball (0 : E) ε ⊆ LocalLog.goodDomain φ := by sorry
