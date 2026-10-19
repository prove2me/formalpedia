-- Prove2me | Theorems.Thm_OAI_C0Absorption_localG_sup
-- name    : OAI.C0Absorption.localG_sup
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T22:02:30.730465+00:00
-- url     : https://prove2.me/theorems/43f9bf18-7798-4ea9-8fcc-eb73e90bdfd7
-- title:
--   Flattening does not increase the sup norm
-- statement:
--   For a centre $q$ and a radius $\varepsilon>0$, the flattening $G_{q,\varepsilon}u=u(q)+\chi(d(\cdot,q)/\varepsilon)(u-u(q))$ freezes $u$ near $q$, and the remainder is $R_{q,\varepsilon}u=G_{q,\varepsilon}u-u$; $\chi(t)=\min(1,\max(0,2t-1))$. If $|u(x)|\le A$ for all $x$, then
--   $$
--   |G_{q,\varepsilon}u(x)|\le A\qquad\text{for all }x .
--   $$
--
--   Flattening a bounded function keeps it bounded by the same constant, so iterated flattenings of base functions stay uniformly bounded.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Analysis/C0Absorption/Localization.lean#L354-L369

import Mathlib
import Definitions.Def_C0Absorption
import Definitions.Def_OAI_Analysis_C0Absorption_Molecules
import Definitions.Def_OAI_Analysis_C0Absorption_Norm
import Definitions.Def_OAI_Analysis_C0Absorption_Completion
import Definitions.Def_OAI_Analysis_C0Absorption_Signs
import Definitions.Def_OAI_Analysis_C0Absorption_Lists
import Definitions.Def_OAI_Analysis_C0Absorption_Pairings
import Definitions.Def_OAI_Analysis_C0Absorption_Localization

open OAI OAI.C0Absorption
open scoped BigOperators NNReal ENNReal
open Finset
open Set Filter Topology

theorem OAI.C0Absorption.localG_sup {X : Type*} [PseudoMetricSpace X] (q : X) (ε : ℝ)
    (u : X → ℝ) (A : ℝ) (hu : ∀ x, |u x| ≤ A) (x : X) :
    |localG q ε u x| ≤ A := by sorry
