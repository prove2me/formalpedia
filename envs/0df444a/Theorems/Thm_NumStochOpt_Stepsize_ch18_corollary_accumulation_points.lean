-- Prove2me | Theorems.Thm_NumStochOpt_Stepsize_ch18_corollary_accumulation_points
-- name    : NumStochOpt.Stepsize.ch18_corollary_accumulation_points
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-02T06:24:06.605808+00:00
-- url     : https://prove2.me/theorems/5ce407ad-8570-4048-8b50-3f85a3ddf3d4
-- title:
--   Ch. 18 Corollary — if $b^s\to0$ a.s., every accumulation point of $\bar x^s$ solves (18.1)
-- statement:
--   Take the setting and hypotheses of Theorem 1 of Chapter 18 (convex $F$ on the convex closed bounded $X\subseteq\mathbb R^n$, the SQG method (18.2) with stochastic quasigradients $E(\xi^s\mid B_s)=F_x(x^s)+b^s$, conditions (18.7), (18.8), (18.10)–(18.13) and condition (1) or (2) on the stepsizes), and assume in addition that $F$ is lower semicontinuous on $X$. If the bias vanishes,
--   $$
--   b^s\to0\quad\text{a.s.},
--   $$
--   then almost surely every accumulation point of the weighted averages $\bar x^s$ of (18.6) is a solution of problem (18.1), i.e. a point $z\in X$ with $F(z)=\min_{x\in X}F(x)$.
--
--   The corollary turns the value estimate of Theorem 1 (with $\bar b=0$) into a statement about the averaged points themselves.
--
--   **Formalization Note** $b^s\to0$ a.s. replaces (18.9); it is (18.9) with $\bar b=0$. Lower semicontinuity of $F$ on $X$ is added: the page assumes only convexity on a closed set, where the corollary can fail (on $X=[0,1]$ the convex function equal to $0$ on $[0,1)$ and $1$ at $1$ admits mean-zero noise under which $\bar x^s\to1$ with positive probability, while $F(\bar x^s)=0$ throughout). For the $F=E_\omega f(x,\omega)$ of the chapter's applications $F$ is continuous. The conventions of Theorem 1 apply.
-- source:
--   S. Uryasev, "Adaptive Stochastic Quasigradient Procedures", in Ermoliev & Wets (eds.), Numerical Techniques for Stochastic Optimization, Springer 1988, Ch. 18, p. 376, Corollary

import Mathlib
import Definitions.Def_NumStochOpt_Stepsize_SQGBasics

open MeasureTheory Filter Topology
open scoped InnerProductSpace ENNReal

namespace NumStochOpt.Stepsize

/-- **Corollary** to Theorem 1 of Uryasev, Ch. 18 of Ermoliev & Wets (1988), p. 376: under the
hypotheses of Theorem 1, if the bias vanishes, `b^s → 0` a.s., then almost surely every
accumulation point of the weighted averages `x̄^s` of (18.6) is a solution of problem (18.1),
i.e. a minimizer of `F` on `X`.

The hypothesis (18.9) of Theorem 1 is replaced by `b^s → 0` a.s. (which is (18.9) with `b̄ = 0`).
Added: `F` is lower semicontinuous on `X`. The page assumes only convexity on the closed set `X`;
without lower semicontinuity the corollary fails (a convex function on `[0, 1]` that is `0` on
`[0, 1)` and `1` at `1` admits noise under which `x̄^s → 1` with positive probability). -/
theorem ch18_corollary_accumulation_points {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : EuclideanSpace ℝ (Fin n) → ℝ) (X : Set (EuclideanSpace ℝ (Fin n)))
    (xstar : EuclideanSpace ℝ (Fin n)) (C₁ C₂ : ℝ)
    (x ξ g b : ℕ → Ω → EuclideanSpace ℝ (Fin n)) (ρ : ℕ → Ω → ℝ)
    (hX_conv : Convex ℝ X) (hX_closed : IsClosed X) (hX_bdd : Bornology.IsBounded X)
    (hF_conv : ConvexOn ℝ X F) (hF_lsc : LowerSemicontinuousOn F X)
    (hxstar : xstar ∈ X ∧ ∀ y ∈ X, F xstar ≤ F y)
    -- the process (18.2) and the stochastic quasigradient condition
    (hx_meas : ∀ s, Measurable (x s)) (hξ_meas : ∀ s, Measurable (ξ s))
    (hξ_int : ∀ s, Integrable (ξ s) μ)
    (hx0 : ∀ ω, x 0 ω ∈ X)
    (hrec : ∀ s ω, x (s + 1) ω = NumStochOpt.QuasiFejer.projX X (x s ω - ρ s ω • ξ s ω))
    (hg : ∀ s, ∀ᵐ ω ∂μ, g s ω ∈ subdiffOn X F (x s ω))
    (hqg : ∀ s, μ[ξ s | histSigma x ξ s s] =ᵐ[μ] fun ω => g s ω + b s ω)
    -- (18.7)
    (h187 : Metric.diam X = C₁)
    -- (18.8)
    (h188 : ∀ s, ∫⁻ ω, ENNReal.ofReal (‖ξ s ω - g s ω - b s ω‖ ^ 2) ∂μ ≤ ENNReal.ofReal (C₂ ^ 2))
    -- the bias vanishes (in place of (18.9))
    (hb : ∀ᵐ ω ∂μ, Tendsto (fun s => b s ω) atTop (𝓝 0))
    -- (18.10)
    (h1810 : ∀ s, ∀ᵐ ω ∂μ, 0 < ρ s ω)
    -- (18.11)
    (h1811 : ∀ s, Integrable (fun ω => ρ s ω ^ 2) μ)
    -- (18.12)
    (h1812 : ∀ᵐ ω ∂μ, Tendsto (fun s => ρ s ω) atTop (𝓝 0))
    -- (18.13)
    (h1813 : ∀ᵐ ω ∂μ, Tendsto (fun N => ∑ s ∈ Finset.range N, ρ s ω) atTop atTop)
    -- condition (1) or condition (2)
    (hregime : (∀ s, Measurable[histSigma x ξ s s] (ρ s)) ∨
      ((∀ᵐ ω ∂μ, Tendsto (fun s => ρ (s + 1) ω / ρ s ω) atTop (𝓝 1)) ∧
        ∀ s, Measurable[histSigma x ξ s (s + 1)] (ρ s))) :
    ∀ᵐ ω ∂μ, ∀ z, MapClusterPt z atTop (fun s => weightedAvg (fun ℓ => ρ ℓ ω) (fun ℓ => x ℓ ω) s) →
      z ∈ X ∧ ∀ y ∈ X, F z ≤ F y := by sorry

end NumStochOpt.Stepsize
