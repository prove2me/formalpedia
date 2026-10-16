-- Prove2me | Theorems.Thm_OAI_Problem310_RoutedExposure_actual_firstDefaultNode_on_atom
-- name    : OAI.Problem310.RoutedExposure.actual_firstDefaultNode_on_atom
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:31:31.289595+00:00
-- url     : https://prove2.me/theorems/fbed8b62-e22a-434e-97c4-0587c4f33401
-- title:
--   A good center exposure fixes the first default stage and node of the route
-- statement:
--   Fix $M,d\in\mathbb{N}$. Finite words over the alphabet $\{0,1,\dots,M\}$ are the vertices of the complete $(M+1)$-ary tree; the letter $M$ is the *default child* and $0,\dots,M-1$ are the *nondefault children*. A *node* is a word $P$ of length $|P|<d$. Let $b$ assign a resolution $b(P,i)\in\mathbb{N}$ to every node $P$ and every $i\in\{0,\dots,M-1\}$. For $\beta\in\mathbb{N}$ and $y\in\mathbb{R}$ put $\kappa_\beta(y)=\lfloor 2^{\beta+2}\{y\}\rfloor\in\{0,\dots,2^{\beta+2}-1\}$, where $\{y\}=y-\lfloor y\rfloor$ is the fractional part.
--
--   A *selector table* $\omega$ assigns a bit $\omega(P,i,c)\in\{\mathrm{true},\mathrm{false}\}$ to every node $P$, every $i<M$ and every $c<2^{b(P,i)+2}$. At a point $y$ the selector of $(P,i)$ reads $\sigma^\omega_{P,i}(y)=\omega(P,i,\kappa_{b(P,i)}(y))$ when $|P|<d$, and $\sigma^\omega_{P,i}(y)=\mathrm{false}$ for longer words. The *first-success rule* chooses at a word $P$ the child $c^\omega(P,y)=\min\{i<M:\sigma^\omega_{P,i}(y)=\mathrm{true}\}$, or the default $M$ if no selector succeeds. The route from the root is $\rho^\omega_0(y)=\varnothing$ (the empty word) and $\rho^\omega_{n+1}(y)=\rho^\omega_n(y)\,c^\omega(\rho^\omega_n(y),y)$ (append the chosen child).
--
--   Fix $x\in\mathbb{R}$. The *center exposure* of $\omega$ is the bit pattern $E_x(\omega)=\bigl(\omega(P,i,\kappa_{b(P,i)}(x))\bigr)_{P,i}$ indexed by all nodes $P$ and all $i<M$: the one entry of each selector table that is read at $x$. For an arbitrary pattern $\xi=(\xi_{P,i})$ let $\bar\omega_\xi$ be the table with $\bar\omega_\xi(P,i,\kappa_{b(P,i)}(x))=\xi_{P,i}$ and all other entries $\mathrm{false}$. Call $\xi$ *good* if the route of $\bar\omega_\xi$ takes the default somewhere, i.e. $c^{\bar\omega_\xi}\bigl(\rho^{\bar\omega_\xi}_k(x),x\bigr)=M$ for some $k<d$.
--
--   **Theorem.** If $\xi$ is good, then there exist a stage $k\in\{0,\dots,d-1\}$ and a node $U$ with $|U|=k$ such that every selector table $\omega$ with $E_x(\omega)=\xi$ satisfies
--
--   $$\rho^\omega_k(x)=U,\qquad c^\omega(U,x)=M,\qquad c^\omega\bigl(\rho^\omega_l(x),x\bigr)\neq M\quad\text{for all }0\le l<k.$$
--
--   Thus on every good exposure atom the route at $x$ takes the default child for the first time at a stage $k$ and a node $U$ that depend only on the exposed bits $\xi$ (and on $x$ and $b$), not on any of the unexposed selector entries. This lets a conditioning argument fix the first-default node before the remaining random coordinates are revealed.
--
--   **Formalization Note** Selector tables are `SelectorTable b`, Boolean functions on the dependent address type `SelectorAddress b`; $E_x$ is `centerExposure b x`, $\bar\omega_\xi$ is `centerCompletion b x ξ`, goodness is `GoodExposure b x ξ`, and $c^\omega(P,y)$ is `selectorChoice b ω P y`, built from `OrderedRouting.chooseChild`. The stage is returned as `k : Fin d` and the node as `U : Node M d`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RoutedExposure.lean#L50-L72

import Mathlib
import Definitions.Def_DyadicAvoidance
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_PeriodicBasic
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_GridSeparation
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_OrderedRouting
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutingPath
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterRouteExposure
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ExceptionalCenters
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFailureBound
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_ConcreteLabelMeasures
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_CenterFirstDefault
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RandomSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedSetDensity
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_RoutedExposure

open OAI OAI.Problem310 OAI.Problem310.RoutedExposure
open FiniteTableModel RoutingPath CenterRouteExposure RoutedSetDensity

theorem OAI.Problem310.RoutedExposure.actual_firstDefaultNode_on_atom {M d : ℕ}
    (b : Node M d → Fin M → ℕ) (x : ℝ) (ξ : Node M d × Fin M → Bool)
    (hgood : GoodExposure b x ξ) :
    ∃ k : Fin d, ∃ U : Node M d, U.val.length = k.val ∧
      ∀ ω : SelectorTable b, centerExposure b x ω = ξ →
        routeFrom (selectorChoice b ω) k.val [] x = U.val ∧
        selectorChoice b ω U.val x = Fin.last M ∧
        ∀ l < k.val,
          selectorChoice b ω (routeFrom (selectorChoice b ω) l [] x) x ≠ Fin.last M := by sorry
