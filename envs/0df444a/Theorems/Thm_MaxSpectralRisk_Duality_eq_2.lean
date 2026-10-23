-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_eq_2
-- name    : MaxSpectralRisk.Duality.eq_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:17.345692+00:00
-- url     : https://prove2.me/theorems/af3fb956-cbed-4946-b21e-67bdc60e50ca
-- title:
--   (2), p. 6 — ES_{α,π}(L) = min_b g_α(b, π) for α ∈ (0, 1), and ES₀ = E_π[L] = inf_b g₀ = lim_{b→−∞} g₀
-- statement:
--   Let $\pi$ be a probability measure on $\mathcal W=\mathcal X\times\mathcal Y$ and $L$ a $\pi$-integrable random variable. With $g_\alpha(b,\pi)=b+(1-\alpha)^{-1}\mathbb E_\pi[(L-b)_+]$ as in (1):
--
--   1. for every $\alpha\in(0,1)$ the minimum of $g_\alpha(\cdot,\pi)$ over $b\in\mathbb R$ is attained and
--   $$\mathrm{ES}_{\alpha,\pi}(L)=\min_{b\in\mathbb R}g_\alpha(b,\pi);$$
--   2. for $\alpha=0$,
--   $$\mathrm{ES}_{0,\pi}(L)=\mathbb E_\pi[L]=\inf_{b\in\mathbb R}g_0(b,\pi)=\lim_{b\to-\infty}g_0(b,\pi).$$
--
--   This is the Rockafellar–Uryasev characterization of Expected Shortfall. It turns the ES-mixture form of $R_{\pi,\sigma}$ into an infimum over threshold functions $\beta(u)$, which is how the dual problem $D_\sigma$ arises.
--
--   **Formalization Note.** "Minimum" is stated as `IsLeast` of the range of $b\mapsto g_\alpha(b,\pi)$; the $\alpha=0$ infimum as `IsGLB` together with the limit at $-\infty$. The paper's remark that the $\alpha=0$ infimum may not be attained is commentary and is not posed. $L$ is assumed measurable (it is a random variable) and integrable.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 6, (1) and (2), and the display after (2) for α = 0

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem eq_2 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (π : Measure (X × Y)) [IsProbabilityMeasure π] (L : X × Y → ℝ) (hLm : Measurable L)
    (hL : Integrable L π) :
    (∀ α ∈ Set.Ioo (0 : ℝ) 1, IsLeast (Set.range fun b => g α b π L) (ES α π L)) ∧
    ES 0 π L = ∫ p, L p ∂π ∧
    IsGLB (Set.range fun b => g 0 b π L) (∫ p, L p ∂π) ∧
    Tendsto (fun b => g 0 b π L) atBot (𝓝 (∫ p, L p ∂π)) := by sorry

end MaxSpectralRisk.Duality
