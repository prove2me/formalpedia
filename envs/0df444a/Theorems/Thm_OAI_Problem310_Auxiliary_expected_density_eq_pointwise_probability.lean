-- Prove2me | Theorems.Thm_OAI_Problem310_Auxiliary_expected_density_eq_pointwise_probability
-- name    : OAI.Problem310.Auxiliary.expected_density_eq_pointwise_probability
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:28:51.021655+00:00
-- url     : https://prove2.me/theorems/1dcea470-ba2a-4bbe-8f5b-abcba1d33d14
-- title:
--   Expected density of a finite random set equals the integral of membership probabilities
-- statement:
--   Let $\Omega$ be a finite set equipped with a $\sigma$-algebra containing all singletons, let $\mu$ be a probability measure on $\Omega$, and let $(R(\omega))_{\omega\in\Omega}$ be a family of Lebesgue measurable subsets of $\mathbb{R}$, i.e. a random measurable set with finitely many possible values. Write $\lambda$ for Lebesgue measure. Then
--   $$\int_\Omega\lambda\bigl(R(\omega)\cap[0,1]\bigr)\,d\mu(\omega)=\int_{[0,1]}\mu\bigl(\{\omega\in\Omega:\ x\in R(\omega)\}\bigr)\,dx .$$
--
--   That is, the expected measure of the random set inside the unit interval equals the integral over $x\in[0,1]$ of the probability that $x$ belongs to it. This Fubini–Tonelli exchange turns pointwise membership probabilities into statements about the expected density of a random set.
--
--   **Formalization Note** Both sides are lower Lebesgue integrals (`lintegral`) of $[0,\infty]$-valued functions, so no integrability assumption is needed.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalExpectation.lean#L13-L32

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

open OAI OAI.Problem310 OAI.Problem310.Auxiliary
universe u_Ω
open Set MeasureTheory

theorem OAI.Problem310.Auxiliary.expected_density_eq_pointwise_probability
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Set ℝ) (hR : ∀ ω, MeasurableSet (R ω)) :
    (∫⁻ ω, volume (R ω ∩ Icc (0 : ℝ) 1) ∂μ) =
      ∫⁻ x in Icc (0 : ℝ) 1, μ {ω | x ∈ R ω} := by sorry
