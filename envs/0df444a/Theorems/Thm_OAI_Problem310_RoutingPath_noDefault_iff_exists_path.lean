-- Prove2me | Theorems.Thm_OAI_Problem310_RoutingPath_noDefault_iff_exists_path
-- name    : OAI.Problem310.RoutingPath.noDefault_iff_exists_path
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:15:53.98302+00:00
-- url     : https://prove2.me/theorems/f8653757-02f5-4e3e-b849-28cc4b81b94c
-- title:
--   No default up to depth $d$ iff the routed word consists of nondefault children
-- statement:
--   Let $M,d\in\mathbb{N}$ and let $X$ be a set of parameters. Children are labelled $0,1,\dots,M$, and $M$ is the *default* child. A decision rule $\operatorname{ch}$ assigns to every finite word $P$ over $\{0,\dots,M\}$ and every $x\in X$ a child $\operatorname{ch}(P,x)\in\{0,\dots,M\}$, and the route of $x$ from the root is $R_0=\varnothing$, $R_{k+1}=R_k\,\operatorname{ch}(R_k,x)$. Then the default is never chosen in the first $d$ steps if and only if the routed word of length $d$ is spelled with nondefault children only:
--   $$\operatorname{ch}(R_k,x)\ne M\ \text{ for all }k<d\iff \exists\, f:\{0,\dots,d-1\}\to\{0,\dots,M-1\}\ \text{ with }\ R_d=\bigl(f(0),f(1),\dots,f(d-1)\bigr).$$
--
--   The function $f$ is the *nondefault path* followed by $x$. The statement identifies the event "no default up to depth $d$" with the set of parameters whose route ends at one of the $M^d$ leaves of the subtree of nondefault children; this is the deterministic event identity needed before the event's probability is computed as a sum over nondefault paths.
--
--   **Formalization Note** The default child is `Fin.last M`, and the word on the right is `List.ofFn (fun i => (f i).castSucc)`, where `Fin.castSucc` embeds $\{0,\dots,M-1\}$ into $\{0,\dots,M\}$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RoutingPath.lean#L160-L191

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

theorem OAI.Problem310.RoutingPath.noDefault_iff_exists_path {M : ℕ}
    (choose : List (Fin (M + 1)) → X → Fin (M + 1)) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ Fin.last M) ↔
      ∃ f : Fin d → Fin M,
        routeFrom choose d [] x = List.ofFn (fun i => (f i).castSucc) := by sorry
