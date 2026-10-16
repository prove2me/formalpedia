-- Prove2me | Theorems.Thm_OAI_Problem310_RoutingPath_noDefault_iff_not_mem
-- name    : OAI.Problem310.RoutingPath.noDefault_iff_not_mem
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:14:23.774252+00:00
-- url     : https://prove2.me/theorems/f87363eb-c331-4ba1-9ee1-9c0c3795b30a
-- title:
--   A route avoids the default at every step iff the default letter is absent from the routed word
-- statement:
--   Let $\iota$ be a set of child labels, $X$ a set of parameters, and $\operatorname{ch}$ a decision rule assigning to every finite word $P$ over $\iota$ and every $x\in X$ a child $\operatorname{ch}(P,x)\in\iota$. Route from the root (the empty word $\varnothing$) by appending the chosen child:
--   $$R_0=\varnothing,\qquad R_{k+1}=R_k\,\operatorname{ch}(R_k,x).$$
--   Fix a distinguished label $\delta\in\iota$ (the *default* child) and a depth $d\in\mathbb{N}$. Then
--   $$\operatorname{ch}(R_k,x)\ne\delta\ \text{ for all } k<d\iff \delta\ \text{does not occur as a letter of the word } R_d .$$
--
--   In words: the default is never chosen during the first $d$ routing decisions exactly when it does not appear in the routed word of length $d$. This converts a statement about the sequence of decisions into a membership statement about the final path, which is the first step in describing the no-default event through the leaves that avoid the default letter.
--
--   **Formalization Note** The routed word is `routeFrom choose d [] x`, and occurrence of $\delta$ is list membership.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RoutingPath.lean#L140-L158

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath

open OAI OAI.Problem310 OAI.Problem310.RoutingPath
universe u_ι u_X
variable {ι : Type u_ι} {X : Type u_X}

theorem OAI.Problem310.RoutingPath.noDefault_iff_not_mem (choose : List ι → X → ι)
    (default : ι) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ default) ↔
      default ∉ routeFrom choose d [] x := by sorry
