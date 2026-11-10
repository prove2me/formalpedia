-- Prove2me | Theorems.Thm_LocalLog_leanlevy_chat31_metricBall_goodDomain
-- name    : LocalLog.leanlevy_chat31_metricBall_goodDomain
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T22:35:19.224411+00:00
-- url     : https://prove2.me/theorems/32ffb64e-b9f9-4658-aa39-ad66c190a06e
-- title:
--   A canonical norm-topology neighbourhood for local characteristic logarithms
-- statement:
--   If φ is continuous in the canonical seminormed topology and φ(0)=1, the preimage of the complex slit plane contains a norm-metric ball. Corrects an independent TopologicalSpace binder in the imported source target.
-- source:
--   https://github.com/slink/LeanLevy/blob/7e73fd9b23ad52956ec2756a815889a783131ce4/LeanLevy/Levy/CharacteristicExponent.lean#L107-L111

import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Definitions.Def_LeanLevy_Levy_CharacteristicExponent
open Topology Filter

theorem LocalLog.leanlevy_chat31_metricBall_goodDomain
    {E : Type*} [SeminormedAddCommGroup E] {φ : E → ℂ}
    (hφ_cont : Continuous φ) (hφ_zero : φ 0 = 1) :
    ∃ ε > 0, Metric.ball (0 : E) ε ⊆ LocalLog.goodDomain φ := by sorry
