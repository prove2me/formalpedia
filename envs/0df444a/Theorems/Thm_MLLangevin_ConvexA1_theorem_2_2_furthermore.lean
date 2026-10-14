-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_theorem_2_2_furthermore
-- name    : MLLangevin.ConvexA1.theorem_2_2_furthermore
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:15.794689+00:00
-- url     : https://prove2.me/theorems/26828863-f18e-44de-a68f-b2a5d826e372
-- title:
--   Theorem 2.2 (15), p. 10 — with Υ̃₁² = σ²α⁻¹d, γ₀ = α/(2L²): error ≲ [f]₁ε at cost ≤ 5log(2L²/α)(L²/α³)σ²dε⁻²⌈log₂(σ²dα⁻¹ε⁻²)⌉³
-- statement:
--   For every $\kappa\in\mathbb R$ there is a constant $\mathfrak C_1$, depending only on $\kappa$, with the following property.
--
--   Work in the setting of Theorem 2.2 ($b$ $L$-Lipschitz with $(\mathbf C_\alpha)$, $\alpha\in(0,L\wedge1]$, $\sigma>0$, independent Brownian motions per level, $\pi$ an invariant probability of the diffusion, $f$ Lipschitz and $\pi$-integrable, $x_0\in\mathbb R^d$) and assume moreover
--   $$\frac\alpha{L^2}\le1,\qquad\sigma^2\alpha^{-1}d\ge1,\qquad|b(x_0)|^2\le\kappa\,\sigma^2\alpha d.$$
--   Run the algorithm of Theorem 2.2 with $\tilde\Upsilon_1^2=\sigma^2\alpha^{-1}d$ in place of $\Upsilon_1^2$ and $\gamma_0=\alpha/(2L^2)$: $R_\varepsilon=\lceil2\log_2(\tilde\Upsilon_1\varepsilon^{-1})\rceil=\lceil\log_2(\frac{\sigma^2d}\alpha\varepsilon^{-2})\rceil$, $T_r=\tilde\Upsilon_1^2\log(\gamma_0^{-1})\alpha^{-1}\varepsilon^{-2}R_\varepsilon^22^{-r}$, $\tau=2\alpha^{-1}|\log\varepsilon|+\alpha^{-1}\log\tilde\Upsilon_1$. For every $\varepsilon\in(0,1)$ with $2\log(\tilde\Upsilon_1\varepsilon^{-2})\le\log(\gamma_0^{-1})R_\varepsilon^2$,
--   $$\big\|\mathcal Y(f)-\pi(f)\big\|_2\le\mathfrak C_1[f]_1\varepsilon,\qquad\mathcal C(\mathcal Y)\le5\log\Big(\frac{2L^2}\alpha\Big)\frac{L^2}{\alpha^3}\sigma^2d\,\varepsilon^{-2}\Big\lceil\log_2\Big(\frac{\sigma^2d}\alpha\varepsilon^{-2}\Big)\Big\rceil^3.$$
--
--   When the drift at the starting point is of the order of the noise, the step can be fixed as $\alpha/(2L^2)$ and the cost is of order $d\,\varepsilon^{-2}\log^3(d\varepsilon^{-2})$.
--
--   **Formalization Note** "$|b(x_0)|^2\lesssim_{uc}\sigma^2\alpha d$" is read as: for each $\kappa$, the constant $\mathfrak C_1$ depends only on $\kappa$. (15) prints the factor $\frac{L^2}{2\alpha^3}$; with these parameters the cost equals $\frac{T_0}{\gamma_0}(1+\frac32R_\varepsilon)\ge3\log(\frac{2L^2}\alpha)\frac{L^2}{\alpha^3}\sigma^2d\varepsilon^{-2}R_\varepsilon^3$, so the printed bound is false; the factor $\frac{L^2}{\alpha^3}$ is what (14) gives at $\gamma_0=\alpha/(2L^2)$, $\Upsilon_1^2=\sigma^2\alpha^{-1}d$.
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Theorem 2.2 (last sentence), (15), p. 10; proof §5.2, p. 36

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Theorem 2.2, "Furthermore" part, (15), p. 10 (constant pinned, see the statement's note):
if `α/L² ≤ 1`, `σ²α⁻¹d ≥ 1` and `|b(x₀)|² ≤ κσ²αd`, the algorithm run with
`Υ̃₁² = σ²α⁻¹d` and `γ₀ = α/(2L²)` has L²-error `≤ 𝔆₁[f]₁ε` (`𝔆₁` depending only on `κ`)
and cost `≤ 5 log(2L²/α)(L²/α³)σ²dε⁻²⌈log₂((σ²d/α)ε⁻²)⌉³`. -/
theorem theorem_2_2_furthermore : ∀ κ : ℝ, ∃ C₁ : ℝ,
    ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → ℝ≥0 → Ω → SDEState d) (_hB : ∀ r, IsStandardBrownian P (B r))
    (_hind : iIndepFun (fun r ω => fun t => B r t ω) P)
    (b : SDEState d → SDEState d) (L α σ : ℝ) (_hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (_hC : CondC b α) (_hα : 0 < α) (_hαL : α ≤ L) (_hα1 : α ≤ 1) (_hσ : 0 < σ)
    (Xsol : SDEState d → ℝ≥0 → Ω → SDEState d)
    (_hX : ∀ x, IsAddSolution b σ (B 0) x (Xsol x))
    (π : Measure (SDEState d)) [IsProbabilityMeasure π] (_hπ : IsInvDiffusion P Xsol π)
    (f : SDEState d → ℝ) (_hf : ∃ K, LipschitzWith K f) (_hfπ : Integrable f π)
    (x₀ : SDEState d) (ε : ℝ)
    (_hαL2 : α / L ^ 2 ≤ 1) (_hσd : 1 ≤ σ ^ 2 * α⁻¹ * (d : ℝ))
    (_hbx₀ : ‖b x₀‖ ^ 2 ≤ κ * (σ ^ 2 * α * (d : ℝ)))
    (_hε : 0 < ε) (_hε1 : ε < 1),
    let γ₀ := α / (2 * L ^ 2)
    let Υ₁ := Real.sqrt (σ ^ 2 * α⁻¹ * (d : ℝ))
    let R := MLLangevin.General.Reps Υ₁ (1 / 2) ε
    let T : ℕ → ℝ := fun r => Υ₁ ^ 2 * Real.log γ₀⁻¹ / α * ε⁻¹ ^ 2 * (R : ℝ) ^ 2 *
      (2 : ℝ) ^ (-(r : ℝ))
    let τ := 2 * α⁻¹ * |Real.log ε| + α⁻¹ * Real.log Υ₁
    2 * Real.log (Υ₁ * ε⁻¹ ^ 2) ≤ Real.log γ₀⁻¹ * (R : ℝ) ^ 2 →
    eLpNorm (fun ω => estimator b σ x₀ γ₀ R τ T B f ω - ∫ x, f x ∂π) 2 P ≤
        ENNReal.ofReal (C₁ * lipConst f * ε) ∧
      cost R γ₀ T ≤ 5 * Real.log (2 * L ^ 2 / α) * (L ^ 2 / α ^ 3) * σ ^ 2 * (d : ℝ) *
        ε⁻¹ ^ 2 * (R : ℝ) ^ 3 := by sorry

end MLLangevin.ConvexA1
