-- Prove2me | Theorems.Thm_JHolomorphic_tendsto_integral_smul_of_bounded
-- name    : JHolomorphic.tendsto_integral_smul_of_bounded
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T13:03:22.41149+00:00
-- url     : https://prove2.me/theorems/7a139d33-47a0-4e32-a432-93732df4b21b
-- title:
--   Convergence of $\int G_n\,w$ for uniformly bounded, eventually compactly located, pointwise convergent weights
-- statement:
--   Let $K\subseteq\mathbb{C}$ be measurable and let $w:\mathbb{C}\to E$ be integrable on $K$, with $E$ a real normed space. Let $G_n:\mathbb{C}\to\mathbb{R}$ be continuous with $|G_n(z)|\le C$ for all $n,z$, let $G_n$ vanish outside $K$ for all sufficiently large $n$, and let $G_n(z)\to g(z)$ for every $z$. Then $\int_{\mathbb{C}}G_n(z)\,w(z)\,dz\to\int_{\mathbb{C}}g(z)\,w(z)\,dz$.
--
--   **Formalization Note** The integrals are Bochner integrals over $\mathbb{C}$ with Lebesgue measure; the limit is along `atTop` in $\mathbb{N}$; `IntegrableOn w K` is integrability on $K$.
-- source:
--   Standard (mollification).

import Definitions.Def_JHolomorphic_Setting
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension

namespace JHolomorphic

open MeasureTheory Filter Topology Metric ContinuousLinearMap
open scoped ContDiff Convolution

/-- Dominated convergence for `∫ Gₙ • w` when the `Gₙ` are uniformly bounded, eventually
supported in a fixed set `K` on which `w` is integrable, and converge pointwise. -/
theorem tendsto_integral_smul_of_bounded {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set ℂ} (hK : MeasurableSet K) {w : ℂ → E} (hw : IntegrableOn w K)
    (G : ℕ → ℂ → ℝ) (g : ℂ → ℝ) (hG : ∀ n, Continuous (G n))
    (hsupp : ∀ᶠ n in atTop, ∀ z ∉ K, G n z = 0) {C : ℝ} (hC : ∀ n z, ‖G n z‖ ≤ C)
    (hlim : ∀ z, Tendsto (fun n => G n z) atTop (𝓝 (g z))) :
    Tendsto (fun n => ∫ z, G n z • w z) atTop (𝓝 (∫ z, g z • w z)) := by
  sorry

end JHolomorphic
