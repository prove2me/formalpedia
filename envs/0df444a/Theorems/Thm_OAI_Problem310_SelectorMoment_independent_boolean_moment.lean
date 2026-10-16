-- Prove2me | Theorems.Thm_OAI_Problem310_SelectorMoment_independent_boolean_moment
-- name    : OAI.Problem310.SelectorMoment.independent_boolean_moment
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:46:13.799835+00:00
-- url     : https://prove2.me/theorems/961725da-8730-46ad-9100-0691eb9de8d9
-- title:
--   Generating function of the number of successes among independent identically distributed Boolean trials
-- statement:
--   Let $(\Omega,\mathcal{F},\mu)$ be a probability space and $I$ a finite set. Bits are written $0$ (false) and $1$ (true). Let $X_i:\Omega\to\{0,1\}$, $i\in I$, be measurable, mutually independent random bits, each with the same law $\nu$ (that is, the image measure of $\mu$ under $X_i$ is $\nu$ for every $i$). Let $N(\omega)=\#\{i\in I:\ X_i(\omega)=1\}$ be the number of successes. Then for every $q\in[0,\infty]$,
--
--   $$\int_\Omega q^{N(\omega)}\,d\mu(\omega)=\big(\nu\{0\}+q\,\nu\{1\}\big)^{|I|}.$$
--
--   This is the probability generating function of a binomial count, evaluated at $q$. It is used with $q$ equal to the probability that a single active test fails: the left side is then the probability that all active tests fail when there are $N$ active tests.
--
--   **Formalization Note** The integral is the lower Lebesgue integral `∫⁻` of a function with values in $[0,\infty]$; $q$ may equal $\infty$, with the conventions $\infty^0=1$ and $0\cdot\infty=0$. Independence is `iIndepFun X μ`, identical distribution is `μ.map (X i) = ν` (no separate assumption that $\nu$ is a probability measure is made), and $N(\omega)$ is the cardinality of the subtype `{i // X i ω = true}`. The σ-algebra on `Bool` is any one with measurable singletons, hence the discrete one.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/SelectorMoment.lean#L19-L45

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

theorem OAI.Problem310.SelectorMoment.independent_boolean_moment
    {Ω : Type u_Ω} {I : Type u_I} [MeasurableSpace Ω] [Fintype I] [DecidableEq I]
    [MeasurableSpace Bool] [MeasurableSingletonClass Bool]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Bool)
    (X : I → Ω → Bool) (hX : iIndepFun X μ)
    (hXm : ∀ i, Measurable (X i)) (hmap : ∀ i, μ.map (X i) = ν)
    (q : ℝ≥0∞) :
    (∫⁻ ω, q ^ Fintype.card {i // X i ω = true} ∂μ) =
      (ν {false} + q * ν {true}) ^ Fintype.card I := by sorry
