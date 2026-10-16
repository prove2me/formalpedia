-- Prove2me | Theorems.Thm_OAI_Problem310_RoutingPath_noDefault_iff_exists_choices
-- name    : OAI.Problem310.RoutingPath.noDefault_iff_exists_choices
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:16:22.304385+00:00
-- url     : https://prove2.me/theorems/2eb744f4-8282-4d46-8ab3-92191e0f1005
-- title:
--   The no-default event is a union of nondefault path cylinders
-- statement:
--   Let $M,d\in\mathbb{N}$, let $X$ be a set of parameters, and label children $0,\dots,M$ with $M$ the *default* child. Let $\operatorname{ch}$ be a decision rule assigning to each finite word $P$ over $\{0,\dots,M\}$ and each $x\in X$ a child $\operatorname{ch}(P,x)$, and route from the root by $R_0=\varnothing$, $R_{k+1}=R_k\,\operatorname{ch}(R_k,x)$. For a function $f:\{0,\dots,d-1\}\to\{0,\dots,M-1\}$ write $f_{<k}=(f(0),\dots,f(k-1))$ for the word of its first $k$ values. Then
--   $$\operatorname{ch}(R_k,x)\ne M\ \text{ for all }k<d\iff\exists\, f:\{0,\dots,d-1\}\to\{0,\dots,M-1\}\ \ \forall k<d:\ \operatorname{ch}(f_{<k},x)=f(k).$$
--
--   So the event that no default is chosen down to depth $d$ is the union, over all $M^d$ nondefault paths $f$, of the *path cylinders* "at the node $f_{<k}$ the rule chooses $f(k)$, for every $k<d$". Each cylinder involves only the decisions at the $d$ nodes of its own path, and distinct paths give disjoint cylinders (a parameter satisfying the cylinder of $f$ has route $f$). In a random model the probability of the no-default event is therefore the sum of the cylinder probabilities.
--
--   **Formalization Note** The word $f_{<k}$ is `(List.ofFn (fun i => (f i).castSucc)).take k`, and the default child is `Fin.last M`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RoutingPath.lean#L193-L212

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

theorem OAI.Problem310.RoutingPath.noDefault_iff_exists_choices {M : ℕ}
    (choose : List (Fin (M + 1)) → X → Fin (M + 1)) (d : ℕ) (x : X) :
    (∀ k < d, choose (routeFrom choose k [] x) x ≠ Fin.last M) ↔
      ∃ f : Fin d → Fin M, ∀ (k : ℕ) (hk : k < d),
        choose ((List.ofFn (fun i => (f i).castSucc)).take k) x =
          (f ⟨k, hk⟩).castSucc := by sorry
