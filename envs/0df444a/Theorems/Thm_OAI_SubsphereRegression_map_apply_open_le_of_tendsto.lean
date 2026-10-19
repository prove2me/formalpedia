-- Prove2me | Theorems.Thm_OAI_SubsphereRegression_map_apply_open_le_of_tendsto
-- name    : OAI.SubsphereRegression.map_apply_open_le_of_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-18T06:17:17.39508+00:00
-- url     : https://prove2.me/theorems/919eed84-693c-44ea-ab47-4799c6c2686a
-- title:
--   Open-set mass bounds survive pointwise limits of measurable maps
-- statement:
--   Let $(X,\mathcal F)$ be a measurable space with a measure $\rho$, and let $Y$ be a topological space with its Borel $\sigma$-algebra and a measure $\tau$. Let $F:X\to Y$ and $F_k:X\to Y$ ($k=0,1,2,\dots$) be measurable maps such that $F_k(x)\to F(x)$ for every $x\in X$. Let $C\in[0,\infty]$ and $\alpha\in\mathbb{R}$, and assume that for every $k$ and every open set $U\subseteq Y$
--   $$\rho\bigl(F_k^{-1}(U)\bigr)\le C\,\tau(U)^{\alpha}.$$
--   Then for every open set $U\subseteq Y$,
--   $$\rho\bigl(F^{-1}(U)\bigr)\le C\,\tau(U)^{\alpha}.$$
--
--   Equivalently, a uniform bound $(F_k)_*\rho(U)\le C\tau(U)^\alpha$ on open sets for the image measures passes to the image measure $F_*\rho$ of the pointwise limit. This is the open-set half of the portmanteau theorem, in a form that needs no finiteness or tightness assumptions; it is used to pass from noisy observation laws to the noiseless one.
--
--   **Formalization Note** Values and powers are in $[0,\infty]$ (for $\alpha<0$ Lean's convention gives $0^{\alpha}=\infty$); the image measures are `ρ.map (Fₖ k)` and `ρ.map F`.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/Subsphere/Regression/Gaussian.lean#L396-L431

import Mathlib
import Definitions.Def_SubsphereCurrent
import Definitions.Def_OAI_Probability_Subsphere_Models
import Definitions.Def_OAI_Probability_Subsphere_Regression_Geometry
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gram
import Definitions.Def_OAI_Probability_Subsphere_Regression_Gaussian

open OAI OAI.SubsphereRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace
universe u
open scoped Topology
open InnerProductSpace
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

theorem OAI.SubsphereRegression.map_apply_open_le_of_tendsto (F : X → Y) (Fₖ : ℕ → X → Y)
    (hF : Measurable F) (hFₖ : ∀ k, Measurable (Fₖ k))
    (ht : ∀ x, Tendsto (fun k => Fₖ k x) atTop (𝓝 (F x)))
    (C : ℝ≥0∞) (α : ℝ)
    (hbound : ∀ k U, IsOpen U → (ρ.map (Fₖ k)) U ≤ C * (τ U)^α)
    (U : Set Y) (hU : IsOpen U) :
    (ρ.map F) U ≤ C * (τ U)^α := by sorry
