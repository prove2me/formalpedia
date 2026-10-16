-- Prove2me | Theorems.Thm_OAI_Problem310_FiniteTableModel_measure_center_no_default_prod
-- name    : OAI.Problem310.FiniteTableModel.measure_center_no_default_prod
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:27:28.895305+00:00
-- url     : https://prove2.me/theorems/70c6ca74-1e3a-4882-bece-0964ba50cbd2
-- title:
--   Center no-default probability $(1-2^{-M})^d$ in the selector-table model with an independent extra factor
-- statement:
--   **Setting.** Fix $M,d\in\mathbb{N}$, children $0,\dots,M$ with default $M$, and call a word $P$ over $\{0,\dots,M\}$ a *node* if $|P|<d$. Let $b$ assign a resolution $b(P,i)\in\mathbb{N}$ to every node $P$ and selector index $i\in\{0,\dots,M-1\}$. For $x\in\mathbb{R}$ write $\kappa_r(x)=\lfloor 2^{r+2}\{x\}\rfloor\in\{0,\dots,2^{r+2}-1\}$ for the dyadic key, where $\{x\}=x-\lfloor x\rfloor$. A *selector table* $\omega$ assigns a bit to every *selector address* $(P,i,k)$ with $P$ a node, $i<M$ and $k<2^{b(P,i)+2}$. At a center $x$ the selector value of a word $P$ and an index $i$ is
--   $$\sigma_{P,i}(\omega,x)=\begin{cases}\omega\bigl(P,i,\kappa_{b(P,i)}(x)\bigr), & |P|<d,\\ \mathrm{false}, & |P|\ge d.\end{cases}$$
--   For a nondefault path $f:\{0,\dots,d-1\}\to\{0,\dots,M-1\}$ let $f_{<k}=(f(0),\dots,f(k-1))$, call the pairs $(k,j)$ with $k<d$ and $0\le j\le f(k)$ its *tests*, and let $r_f(k,j)$ be $\mathrm{true}$ if $j=f(k)$ and $\mathrm{false}$ if $j<f(k)$.
--
--   **Theorem.** Let $\nu$ be a probability measure on $\{\mathrm{true},\mathrm{false}\}$ giving mass $\tfrac12$ to each bit, let $\nu^{\otimes}$ be the product measure (independent $\nu$-distributed entries) on selector tables, and let $\tau$ be any probability measure on a measurable space $T$. Then for every $x\in\mathbb{R}$,
--   $$\bigl(\nu^{\otimes}\otimes\tau\bigr)\Bigl(\bigcup_{f}\bigl\{(\omega,s):\ \sigma_{f_{<k},j}(\omega,x)=r_f(k,j)\ \text{for all tests }(k,j)\text{ of }f\bigr\}\Bigr)=\bigl(1-2^{-M}\bigr)^d,$$
--   the union running over all nondefault paths $f$.
--
--   The event says that first-success routing at the center $x$, reading each selector table at the dyadic cell of $x$, follows some nondefault path down to depth $d$. Its probability is the same for every center and every choice of resolutions, and adjoining an independent second component (in the application, the terminal tables) does not change it. This is the exact no-default probability used when bounding failure probabilities at a fixed center.
--
--   **Formalization Note** Selector tables are functions `SelectorAddress b → Bool` with law `Measure.pi (fun _ => ν)`; the second factor $T$ is arbitrary, and the event does not depend on its coordinate $s$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/CenterFirstDefault.lean#L44-L69

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

open OAI OAI.Problem310 OAI.Problem310.FiniteTableModel
universe u_T
open MeasureTheory ProbabilityTheory

theorem OAI.Problem310.FiniteTableModel.measure_center_no_default_prod {M d : ℕ}
    {T : Type u_T} [MeasurableSpace T] (τ : Measure T) [IsProbabilityMeasure τ]
    (b : Node M d → Fin M → ℕ)
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ bit, ν {bit} = (2 : ENNReal)⁻¹) (x : ℝ) :
    ((Measure.pi (fun _ : SelectorAddress b => ν)).prod τ)
      (⋃ f : FirstDefault.Path M d, {ω : SelectorTable b × T |
        ∀ i : FirstDefault.Tests f,
        selectorValue b ω.1 (FirstDefault.address f i).1 (FirstDefault.address f i).2 x =
          FirstDefault.requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by sorry
