-- Prove2me | Theorems.Thm_NetTraffic_PoissonFBM_G_stationary_increments
-- name    : NetTraffic.PoissonFBM.G_stationary_increments
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T02:14:52.608536+00:00
-- url     : https://prove2.me/theorems/cd522f00-352f-4a1c-9f73-fd598a9da02a
-- title:
--   §6.3, p. 58 — G_T has stationary increments: (G_T(t+h) − G_T(h))_{t≥0} =d (G_T(t))_{t≥0}
-- statement:
--   Let $F_{\mathrm{on}}$ satisfy (2.8) with $1<\alpha<2$, let $\lambda(T)>0$, and for each $T$ consider the infinite source Poisson model with rate $\lambda(T)$. Let
--   $$G_T(t)=\frac{A(Tt)-\lambda\mu_{\mathrm{on}}Tt}{[\lambda T^3\bar F_{\mathrm{on}}(T)\sigma^2]^{1/2}},\qquad t\ge0 .$$
--   For every $T>0$ and every $h>0$,
--   $$\{G_T(t+h)-G_T(h),\ t\ge0\}\overset{d}{=}\{G_T(t),\ t\ge0\},$$
--   as processes: the two have the same finite-dimensional distributions. This follows from the stationarity of the input rate $N$, and reduces fourth moments of increments of $G_T$ to fourth moments of $G_T(u)$.
--
--   **Formalization Note** Both processes are random elements of $\mathbb R^{[0,\infty)}$ with the product σ-algebra, whose laws are determined by the finite-dimensional distributions; their measurability is part of the statement, so that the equality of image measures is not vacuous.
-- source:
--   Mikosch, Resnick, Rootzén and Stegeman, Is network traffic approximated by stable Lévy motion or fractional Brownian motion?, Ann. Appl. Probab. 12 (2002), p. 58, §6.3, display after "We also know that for any h > 0"

import Mathlib
import Definitions.Def_NetTraffic_PoissonFBM_Setting

open MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal

namespace NetTraffic.PoissonFBM

/-- §6.3, p. 58: for each `T > 0` and `h > 0`, the process `(G_T(t + h) - G_T(h))_{t ≥ 0}` has
the same law as `(G_T(t))_{t ≥ 0}` (laws on `ℝ^{[0,∞)}` with the product σ-algebra, i.e. all
finite-dimensional distributions agree): `G_T` has stationary increments. -/
theorem G_stationary_increments
    (Fon : Measure ℝ) [IsProbabilityMeasure Fon] (α : ℝ) (hF : NetTraffic.PoissonStable.HeavyTail Fon α)
    (lam : ℝ → ℝ) (hlam : ∀ T, 0 < lam T) (hmono : Monotone lam)
    (Ω : ℝ → Type*) [∀ T, MeasurableSpace (Ω T)] (P : ∀ T, Measure (Ω T))
    [∀ T, IsProbabilityMeasure (P T)] (Γ X : ∀ T, ℤ → Ω T → ℝ)
    (hmodel : ∀ T, NetTraffic.PoissonStable.IsPoissonModel (P T) (lam T) Fon (Γ T) (X T))
    (T : ℝ) (hT : 0 < T) (h : ℝ≥0) (hh : 0 < h) :
    AEMeasurable (fun ω (t : ℝ≥0) => G Fon α lam (Γ T) (X T) T (t + h) ω -
      G Fon α lam (Γ T) (X T) T h ω) (P T) ∧
    AEMeasurable (fun ω (t : ℝ≥0) => G Fon α lam (Γ T) (X T) T t ω) (P T) ∧
    (P T).map (fun ω (t : ℝ≥0) => G Fon α lam (Γ T) (X T) T (t + h) ω -
        G Fon α lam (Γ T) (X T) T h ω) =
      (P T).map (fun ω (t : ℝ≥0) => G Fon α lam (Γ T) (X T) T t ω) := by sorry

end NetTraffic.PoissonFBM
