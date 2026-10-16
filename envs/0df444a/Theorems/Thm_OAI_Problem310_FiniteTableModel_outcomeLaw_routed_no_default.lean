-- Prove2me | Theorems.Thm_OAI_Problem310_FiniteTableModel_outcomeLaw_routed_no_default
-- name    : OAI.Problem310.FiniteTableModel.outcomeLaw_routed_no_default
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:32:49.631487+00:00
-- url     : https://prove2.me/theorems/2d99dde1-db9b-462c-a92a-7f8daf5faede
-- title:
--   The routed path avoids the default child with probability exactly $(1-2^{-M})^d$
-- statement:
--   Fix $M,d\in\mathbb{N}$. Finite words over $\{0,1,\dots,M\}$ are the vertices of the complete $(M+1)$-ary tree, and the letter $M$ is the *default child*. A *node* is a word of length $<d$ and a *leaf* is a word of length exactly $d$. For $\beta\in\mathbb{N}$ and $y\in\mathbb{R}$ let $\kappa_\beta(y)=\lfloor 2^{\beta+2}\{y\}\rfloor\in\{0,\dots,2^{\beta+2}-1\}$, where $\{y\}=y-\lfloor y\rfloor$.
--
--   Let $b_S$ assign a resolution $b_S(P,i)\in\mathbb{N}$ to every node $P$ and every $i<M$, and let $b_T$ assign a resolution $b_T(L)\in\mathbb{N}$ to every leaf $L$. A *selector table* $\omega_S$ assigns a bit to every address $(P,i,c)$ with $c<2^{b_S(P,i)+2}$, and a *terminal table* $\omega_T$ assigns a bit to every address $(L,c)$ with $c<2^{b_T(L)+2}$. At a point $y$ the selector of $(P,i)$ reads $\sigma_{P,i}(y)=\omega_S(P,i,\kappa_{b_S(P,i)}(y))$ (and $\mathrm{false}$ if $|P|\ge d$); the first-success rule chooses $c(P,y)=\min\{i<M:\sigma_{P,i}(y)=\mathrm{true}\}$, or the default $M$ if no selector succeeds; and the route from the root is $\rho_0(y)=\varnothing$, $\rho_{n+1}(y)=\rho_n(y)\,c(\rho_n(y),y)$.
--
--   Let $0\le p\le1$, and let $\mu_p$ be the probability law on pairs $(\omega_S,\omega_T)$ under which all selector bits and all terminal bits are independent, each selector bit is $\mathrm{true}$ with probability $\tfrac12$, and each terminal bit is $\mathrm{true}$ with probability $p$.
--
--   **Theorem.** For every $x\in\mathbb{R}$,
--
--   $$\mu_p\Bigl(\bigl\{(\omega_S,\omega_T):\ \text{the letter } M \text{ does not occur in the word } \rho_d(x)\bigr\}\Bigr)=\bigl(1-2^{-M}\bigr)^d .$$
--
--   So the depth-$d$ route at a fixed point never takes the default child with probability exactly $(1-2^{-M})^d$, whatever the resolutions $b_S,b_T$, the point $x$ and the terminal parameter $p$; equivalently, a default occurs somewhere on the route with probability $1-(1-2^{-M})^d$. The identity holds for all $M,d\ge0$; for instance, when $M=0$ every decision is the default and both sides vanish for $d\ge1$.
--
--   **Formalization Note** The law $\mu_p$ is `ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1`, the product of a `Measure.pi` of fair Bernoulli bits on selector addresses with a `Measure.pi` of Bernoulli bits of parameter $p$ on terminal addresses; the hypotheses `hp0`, `hp1` are needed to form the Bernoulli law. Probabilities take values in `ENNReal`, where the subtraction $1-2^{-M}$ is truncated at $0$, which is harmless since $2^{-M}\le1$. The route is `RoutingPath.routeFrom` with the decision `OrderedRouting.chooseChild` applied to `selectorValue bS ω.1 P i y`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/RoutedFirstDefault.lean#L10-L32

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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FirstDefaultSelection

open OAI OAI.Problem310 OAI.Problem310.FiniteTableModel

theorem OAI.Problem310.FiniteTableModel.outcomeLaw_routed_no_default {M d : ℕ}
    (bS : Node M d → Fin M → ℕ) (bT : Leaf M d → ℕ)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (x : ℝ) :
    (ConcreteLabels.outcomeLaw (SelectorAddress bS) (TerminalAddress bT) p hp0 hp1)
      {ω : SelectorTable bS × TerminalTable bT |
        Fin.last M ∉ RoutingPath.routeFrom
          (fun P y => OrderedRouting.chooseChild (fun i => selectorValue bS ω.1 P i y))
          d [] x} = (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by sorry
