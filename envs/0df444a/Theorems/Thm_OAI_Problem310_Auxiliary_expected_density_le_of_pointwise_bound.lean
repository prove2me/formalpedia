-- Prove2me | Theorems.Thm_OAI_Problem310_Auxiliary_expected_density_le_of_pointwise_bound
-- name    : OAI.Problem310.Auxiliary.expected_density_le_of_pointwise_bound
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-16T04:29:18.821381+00:00
-- url     : https://prove2.me/theorems/2b1c11e4-3166-4d7d-8ab4-60e2b2498cb8
-- title:
--   Expected density bound from a pointwise membership bound off an exceptional set
-- statement:
--   Let $\Omega$ be a finite set with a $\sigma$-algebra containing all singletons, $\mu$ a probability measure on $\Omega$, and $(R(\omega))_{\omega\in\Omega}$ a family of Lebesgue measurable subsets of $\mathbb{R}$. Write $\lambda$ for Lebesgue measure. Let $G\subseteq\mathbb{R}$ be a measurable set and $\alpha\in[0,\infty]$, and assume that every point of $G$ belongs to the random set with probability at most $\alpha$:
--   $$\mu\bigl(\{\omega:\ x\in R(\omega)\}\bigr)\le\alpha\qquad\text{for all }x\in G .$$
--   Then, with $G^{\mathrm c}=\mathbb{R}\setminus G$,
--   $$\int_\Omega\lambda\bigl(R(\omega)\cap[0,1]\bigr)\,d\mu(\omega)\le\alpha+\lambda\bigl(G^{\mathrm c}\cap[0,1]\bigr).$$
--
--   So a uniform pointwise membership bound outside a small exceptional set of points controls the expected density of the random set on $[0,1]$. This is the integration step that converts pointwise failure probabilities into a bound on the expected size of a random set of bad centers.
--
--   **Formalization Note** The left-hand side is a lower Lebesgue integral and $\alpha$ is an extended nonnegative real (`ENNReal`).
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/MeasureTheory/DyadicAvoidance/ExceptionalExpectation.lean#L34-L56

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

theorem OAI.Problem310.Auxiliary.expected_density_le_of_pointwise_bound
    {Ω : Type u_Ω} [Fintype Ω] [MeasurableSpace Ω] [MeasurableSingletonClass Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (R : Ω → Set ℝ) (hR : ∀ ω, MeasurableSet (R ω))
    (G : Set ℝ) (hG : MeasurableSet G) (a : ENNReal)
    (hgood : ∀ x ∈ G, μ {ω | x ∈ R ω} ≤ a) :
    (∫⁻ ω, volume (R ω ∩ Icc (0 : ℝ) 1) ∂μ) ≤
      a + volume (Gᶜ ∩ Icc (0 : ℝ) 1) := by sorry
