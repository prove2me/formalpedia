-- Prove2me | Theorems.Thm_OAI_Problem310_FirstDefault_measure_no_default_finite_table
-- name    : OAI.Problem310.FirstDefault.measure_no_default_finite_table
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:25:09.975759+00:00
-- url     : https://prove2.me/theorems/e34cd7fc-b5e2-4885-89cb-52cf972c1e6c
-- title:
--   Exact no-default probability for fair product tables read at distinct coordinates
-- statement:
--   Fix $M,d\in\mathbb{N}$ and label children $0,\dots,M$ (child $M$ is the *default*). A *bounded address* is a pair $(P,i)$ with $P$ a word over $\{0,\dots,M\}$ of length $|P|<d$ and $i\in\{0,\dots,M-1\}$. A *nondefault path* is a function $f:\{0,\dots,d-1\}\to\{0,\dots,M-1\}$, with prefixes $f_{<k}=(f(0),\dots,f(k-1))$; its *tests* are the pairs $(k,j)$ with $k<d$ and $0\le j\le f(k)$, the test $(k,j)$ reading the address $(f_{<k},j)$ and requiring the bit $r_f(k,j)$, equal to $\mathrm{true}$ if $j=f(k)$ and to $\mathrm{false}$ if $j<f(k)$.
--
--   Let $K$ be a finite set, $\nu$ a probability measure on $\{\mathrm{true},\mathrm{false}\}$ with $\nu(\{\mathrm{true}\})=\nu(\{\mathrm{false}\})=\tfrac12$, and $\nu^{\otimes K}$ the product measure on tables $\omega\in\{\mathrm{true},\mathrm{false}\}^K$. Let $c$ be an injective map from bounded addresses to $K$ (the coordinate at which each address is stored). Then
--   $$\nu^{\otimes K}\Bigl(\bigcup_{f}\bigl\{\omega:\ \omega\bigl(c(f_{<k},j)\bigr)=r_f(k,j)\ \text{for all tests }(k,j)\text{ of }f\bigr\}\Bigr)=\bigl(1-2^{-M}\bigr)^d,$$
--   the union running over all nondefault paths $f$.
--
--   This transfers the exact survival probability of first-success routing to concrete random tables of independent fair bits: as long as distinct addresses are stored at distinct coordinates, the probability that the routing avoids the default for $d$ levels is $(1-2^{-M})^d$, and the table entries that are never read play no role.
--
--   **Formalization Note** The product measure is `Measure.pi (fun _ : K => ν)`, and the right-hand side is an extended nonnegative real.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/FiniteTableFirstDefault.lean#L12-L34

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
universe u_K
open MeasureTheory ProbabilityTheory

theorem OAI.Problem310.FirstDefault.measure_no_default_finite_table {M d : ℕ} {K : Type u_K} [Fintype K]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfair : ∀ b, ν {b} = (2 : ENNReal)⁻¹)
    (center : BoundedAddress M d → K) (hinj : Function.Injective center) :
    (Measure.pi (fun _ : K => ν))
        (⋃ f : Path M d, {ω | ∀ i : Tests f,
          ω (center (boundedAddress f i)) = requiredBit f i}) =
      (1 - ((2 : ENNReal)⁻¹) ^ M) ^ d := by sorry
