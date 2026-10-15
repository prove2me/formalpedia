-- Prove2me | Theorems.Thm_OAI_NoiselessRegression_map_apply_open_le_of_tendsto
-- name    : OAI.NoiselessRegression.map_apply_open_le_of_tendsto
-- status  : Proved
-- author  : @Shuze Chen
-- created : 2026-10-15T09:29:12.278071+00:00
-- url     : https://prove2.me/theorems/72b690fc-0767-4db3-962d-abb9b1df9c3e
-- title:
--   Bounds on open sets pass to pointwise limits of measurable maps
-- statement:
--   Let $(X,\mathcal A)$ be a measurable space with a measure $\rho$, and let $Y$ be a topological space carrying its Borel $\sigma$-algebra and a measure $\tau$. Let $F:X\to Y$ and $F_k:X\to Y$ $(k\in\mathbb N)$ be measurable maps such that $F_k(x)\to F(x)$ for every $x\in X$, and let $C\in[0,\infty]$ and $\alpha\in\mathbb R$. Suppose that for every $k$ and every open set $U\subseteq Y$ one has $\rho\big(F_k^{-1}(U)\big)\le C\,\tau(U)^{\alpha}$. Then for every open set $U\subseteq Y$,
--
--   $$
--   \rho\big(F^{-1}(U)\big)\le C\,\tau(U)^{\alpha}.
--   $$
--
--   In terms of image measures: if $(F_k)_{\#}\rho(U)\le C\,\tau(U)^{\alpha}$ for all open $U$, uniformly in $k$, then the same bound holds for $F_{\#}\rho$. This is the portmanteau-type lower semicontinuity of the masses of open sets. It is used to transfer estimates from noisy observation laws to their noiseless limit.
--
--   **Formalization Note** Measures take values in $[0,\infty]$, and $\tau(U)^{\alpha}$ is the extended-real power with Mathlib's conventions (for instance $0^{\alpha}=\infty$ when $\alpha<0$). No finiteness assumption is made on $\rho$ or $\tau$.
-- source:
--   https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Probability/GaussianRegression/Smoothing.lean#L171-L205

import Mathlib
import Definitions.Def_NoiselessRegression
import Definitions.Def_OAI_Probability_ProjectionMoments_Model
import Definitions.Def_OAI_Probability_GaussianRegression_Nets
import Definitions.Def_OAI_Probability_GaussianRegression_Gram
import Definitions.Def_OAI_Probability_GaussianRegression_ReplicaMoments
import Definitions.Def_OAI_Probability_GaussianRegression_Smoothing

open OAI OAI.NoiselessRegression
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal RealInnerProductSpace Topology
open InnerProductSpace
universe u
variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [TopologicalSpace Y] [BorelSpace Y]
  (ρ : Measure X) (τ : Measure Y)

theorem OAI.NoiselessRegression.map_apply_open_le_of_tendsto (F : X → Y) (Fₖ : ℕ → X → Y)
    (hF : Measurable F) (hFₖ : ∀ k, Measurable (Fₖ k))
    (ht : ∀ x, Tendsto (fun k => Fₖ k x) atTop (𝓝 (F x)))
    (C : ℝ≥0∞) (α : ℝ)
    (hbound : ∀ k U, IsOpen U → (ρ.map (Fₖ k)) U ≤ C * (τ U)^α)
    (U : Set Y) (hU : IsOpen U) :
    (ρ.map F) U ≤ C * (τ U)^α := by sorry
