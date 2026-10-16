-- Prove2me | Theorems.Thm_OAI_Problem310_SelectorMoment_lookup_fair_failure_moment
-- name    : OAI.Problem310.SelectorMoment.lookup_fair_failure_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:48:32.626355+00:00
-- url     : https://prove2.me/theorems/d61d2853-dec9-4ef0-a0d4-a37d04d7fdf9
-- title:
--   Failure moment of injectively addressed fair bits equals $(1-p/2)^{|I|}$
-- statement:
--   Let $I$ and $K$ be finite sets, and let $\nu$ be the fair probability measure on $\{0,1\}$ (bits $0$ = false, $1$ = true), $\nu\{0\}=\nu\{1\}=\tfrac12$. Equip $\{0,1\}^K$ with the product measure $\nu^{\otimes K}$, under which the coordinates $\omega_k$, $k\in K$, are independent fair bits. Let $\mathrm{addr}:I\to K$ be injective and $p\le 1$ a real number, and let $N(\omega)=\#\{i\in I:\ \omega_{\mathrm{addr}(i)}=1\}$ count the indices whose addressed coordinate is $1$. Then
--
--   $$\int_{\{0,1\}^K}(1-p)^{N(\omega)}\,d\nu^{\otimes K}(\omega)=\Big(1-\frac p2\Big)^{|I|}.$$
--
--   Interpretation: if each of $|I|$ distinct fair selector entries activates a test with probability $\tfrac12$, and each active test independently fails with probability $1-p$, then the probability that all active tests fail is $(1-p/2)^{|I|}$. This is the exact per-trial factor in the fixed-scale miss probability.
--
--   **Formalization Note** Both sides are elements of $[0,\infty]$: the bases are `ENNReal.ofReal (1 - p)` and `ENNReal.ofReal (1 - p / 2)`, which equal $1-p$ and $1-p/2$ because $p\le1$ (negative $p$ is allowed). The integral is the lower Lebesgue integral with respect to `Measure.pi (fun _ : K => ν)`. The σ-algebra on `Bool` is any one with measurable singletons, hence the discrete one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/SelectorMoment.lean#L77-L100

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
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_FiniteLocalPredicate
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowData
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTableModel
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_StableRoutingBridge
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowExceptionalTransfer
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_TrialAddresses
import Definitions.Def_OAI_MeasureTheory_DyadicAvoidance_WindowTrialAddresses

open OAI OAI.Problem310
universe u_I u_Ω u_K
open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

theorem OAI.Problem310.SelectorMoment.lookup_fair_failure_moment
    {I : Type u_I} {K : Type u_K} [Fintype I] [DecidableEq I] [Fintype K]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (ν : Measure Bool) [IsProbabilityMeasure ν]
    (hfalse : ν {false} = 1 / 2) (htrue : ν {true} = 1 / 2)
    (addr : I → K) (hinj : Function.Injective addr)
    (p : ℝ) (hp : p ≤ 1) :
    (∫⁻ ω : K → Bool, (ENNReal.ofReal (1 - p)) ^ Fintype.card {i // ω (addr i) = true}
      ∂(Measure.pi (fun _ : K => ν))) =
      (ENNReal.ofReal (1 - p / 2)) ^ Fintype.card I := by sorry
