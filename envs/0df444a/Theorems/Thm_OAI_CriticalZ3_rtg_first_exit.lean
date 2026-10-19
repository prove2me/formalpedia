-- Prove2me | Theorems.Thm_OAI_CriticalZ3_rtg_first_exit
-- name    : OAI.CriticalZ3.rtg_first_exit
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T18:44:21.485234+00:00
-- url     : https://prove2.me/theorems/574d329e-ccbe-48ac-899c-eafda5c49a77
-- title:
--   A path leaving a set has a first exit step
-- statement:
--   Let $r$ be a relation on $V$, $D\subseteq V$, and suppose $x\in D$ is joined to $y\notin D$ by an $r$-path. Then there are $a\in D$ and $b\notin D$ with $r(a,b)$ such that $x$ reaches $a$ by an $r$-path staying in $D$:
--   $$
--   x\leadsto a\ \text{within }D,\qquad r(a,b),\qquad b\notin D .
--   $$
--
--   So every path leaving $D$ does so through a first exit step.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/CriticalZ3/Basic.lean#L558-L573

import Mathlib
import Definitions.Def_CriticalZ3
import Definitions.Def_OAI_Probability_CriticalZ3_Basic

open OAI OAI.CriticalZ3
universe uE uOmega uV
open MeasureTheory ProbabilityTheory
open Filter
open scoped Topology

theorem OAI.CriticalZ3.rtg_first_exit {V : Type uV} {r : V → V → Prop} {D : Set V} {x y : V}
    (h : Relation.ReflTransGen r x y) (hx : x ∈ D) (hy : y ∉ D) :
    ∃ a ∈ D, ∃ b ∉ D, Relation.ReflTransGen (Within D r) x a ∧ r a b := by sorry
