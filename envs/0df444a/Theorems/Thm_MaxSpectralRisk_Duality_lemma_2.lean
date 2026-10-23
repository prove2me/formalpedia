-- Prove2me | Theorems.Thm_MaxSpectralRisk_Duality_lemma_2
-- name    : MaxSpectralRisk.Duality.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T23:07:36.108331+00:00
-- url     : https://prove2.me/theorems/2c1e3816-a8c8-441a-a67d-3d98e2ef25b1
-- title:
--   Lemma 2, p. 9 — g_α(·, π) is convex and coercive, with ∂₁g_α(b, π) = [1 − π(L ≥ b)/(1 − α), 1 − π(L > b)/(1 − α)] and its argmin
-- statement:
--   Let $\alpha\in(0,1)$, $\pi$ a probability measure on $\mathcal W$ and $L\in\mathcal L^1(\pi)$, and let $g_\alpha(\cdot,\pi):\mathbb R\to\mathbb R$ be defined by (1). Then $g_\alpha(\cdot,\pi)$ is convex, $\lim_{b\to\pm\infty}g_\alpha(b,\pi)=\infty$, and for every $b$
--   $$\partial_1g_\alpha(b,\pi)=\Big[1-\tfrac{\pi(L\ge b)}{1-\alpha},\ 1-\tfrac{\pi(L>b)}{1-\alpha}\Big],\qquad \operatorname{argmin}g_\alpha(\cdot,\pi)=\{b:\pi(L>b)\le1-\alpha\le\pi(L\ge b)\},$$
--   where $\partial_1g_\alpha(b,\pi)$ is the subdifferential of $g_\alpha(\cdot,\pi)$ at $b$.
--
--   The minimizers of $g_\alpha$ are the $\alpha$-quantiles of $L$ under $\pi$; this is what identifies the pointwise minimizers in Lemma 4.
--
--   **Formalization Note.** The subdifferential is written out as $\{s:\ g_\alpha(b')\ge g_\alpha(b)+s(b'-b)\ \forall b'\}$ and the argmin as the set of global minimizers. $L$ is measurable and $\pi$-integrable.
-- source:
--   Ghossoub, Hall, Saunders, Maximum Spectral Measures of Risk with given Risk Factor Marginal Distributions, arXiv:2010.14673v1, p. 9, Lemma 2

import Mathlib
import Definitions.Def_MongeKantorovichYao_Defs
import Definitions.Def_MaxSpectralRisk_Duality_Setting

namespace MaxSpectralRisk.Duality

open MeasureTheory Filter Topology

theorem lemma_2 {X Y : Type*} [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X]
    [TopologicalSpace Y] [PolishSpace Y] [MeasurableSpace Y] [BorelSpace Y]
    (α : ℝ) (hα : α ∈ Set.Ioo (0 : ℝ) 1) (π : Measure (X × Y)) [IsProbabilityMeasure π]
    (L : X × Y → ℝ) (hLm : Measurable L) (hL : Integrable L π) :
    ConvexOn ℝ Set.univ (fun b => g α b π L) ∧
    Tendsto (fun b => g α b π L) atTop atTop ∧
    Tendsto (fun b => g α b π L) atBot atTop ∧
    (∀ b : ℝ, {s : ℝ | ∀ b' : ℝ, g α b π L + s * (b' - b) ≤ g α b' π L} =
      Set.Icc (1 - (1 - α)⁻¹ * π.real {p | b ≤ L p}) (1 - (1 - α)⁻¹ * π.real {p | b < L p})) ∧
    {b : ℝ | ∀ b' : ℝ, g α b π L ≤ g α b' π L} =
      {b : ℝ | π.real {p | b < L p} ≤ 1 - α ∧ 1 - α ≤ π.real {p | b ≤ L p}} := by sorry

end MaxSpectralRisk.Duality
