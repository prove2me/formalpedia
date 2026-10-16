-- Prove2me | Theorems.Thm_OAI_Problem310_FirstDefault_measure_no_default_bounded
-- name    : OAI.Problem310.FirstDefault.measure_no_default_bounded
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:22:29.964981+00:00
-- url     : https://prove2.me/theorems/24419db0-4374-48e4-bad4-d903b022c08b
-- title:
--   First-success routing with fair independent selectors avoids the default for $d$ levels with probability $(1-2^{-M})^d$
-- statement:
--   **Setting.** Fix $M,d\in\mathbb{N}$ and label children $0,\dots,M$ (child $M$ is the *default*). An *address* is a pair $(P,i)$ of a word $P$ over $\{0,\dots,M\}$ and a selector index $i\in\{0,\dots,M-1\}$; it is *bounded* if $|P|<d$. A *nondefault path* is a function $f:\{0,\dots,d-1\}\to\{0,\dots,M-1\}$; there are $M^d$ of them. For $k<d$ let $f_{<k}=(f(0),\dots,f(k-1))$, and call the pairs $(k,j)$ with $k<d$ and $0\le j\le f(k)$ the *tests* of $f$. The test $(k,j)$ reads the bounded address $(f_{<k},j)$ and requires the bit
--   $$r_f(k,j)=\begin{cases}\mathrm{true}, & j=f(k),\\ \mathrm{false}, & j<f(k).\end{cases}$$
--   Given Boolean selectors $S_a$, the *cylinder* of $f$ is the event that all tests of $f$ pass: at every node $f_{<k}$ the selectors $0,\dots,f(k)-1$ are false and selector $f(k)$ is true, i.e. first-success routing follows $f$.
--
--   **Theorem.** Let $(\Omega,\mathcal F,\mu)$ be a measure space and let $(S_a)$ be a family of measurable maps $S_a:\Omega\to\{\mathrm{true},\mathrm{false}\}$, indexed by the bounded addresses, which is mutually independent under $\mu$ and fair: $\mu(S_a=\mathrm{true})=\mu(S_a=\mathrm{false})=\tfrac12$ for every $a$. Then
--   $$\mu\Bigl(\bigcup_{f}\bigl\{\omega\in\Omega:\ S_{(f_{<k},j)}(\omega)=r_f(k,j)\ \text{for all tests }(k,j)\text{ of }f\bigr\}\Bigr)=\bigl(1-2^{-M}\bigr)^d,$$
--   the union running over all nondefault paths $f:\{0,\dots,d-1\}\to\{0,\dots,M-1\}$.
--
--   The union is the event that first-success routing driven by independent fair selectors avoids the default child for $d$ consecutive levels, so this is the exact survival probability of the routing: at each level the default is chosen exactly when all $M$ selectors at the current node fail, which has probability $2^{-M}$. Only the selectors at nodes of depth less than $d$ are involved.
--
--   **Formalization Note** Mathlib's mutual independence `iIndepFun` includes the product rule for the empty family, which already forces $\mu(\Omega)=1$, so no separate probability-measure assumption appears. Measures and the right-hand side are extended nonnegative reals.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/FirstDefault.lean#L202-L234

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

open OAI OAI.Problem310 OAI.Problem310.FirstDefault
universe u_Ω
open MeasureTheory ProbabilityTheory
open scoped BigOperators

theorem OAI.Problem310.FirstDefault.measure_no_default_bounded {M d : ℕ} {Ω : Type u_Ω} [MeasurableSpace Ω]
    (μ : Measure Ω) (S : BoundedAddress M d → Ω → Bool)
    (hS : ∀ a, Measurable (S a)) (hIndep : iIndepFun S μ)
    (hfair : ∀ a b, μ (S a ⁻¹' {b}) = (2 : ENNReal)⁻¹) :
    μ (⋃ f : Path M d,
      {ω | ∀ i : Tests f, S (boundedAddress f i) ω = requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by sorry
