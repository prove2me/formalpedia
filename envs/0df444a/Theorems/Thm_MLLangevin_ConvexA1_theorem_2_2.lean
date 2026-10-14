-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_theorem_2_2
-- name    : MLLangevin.ConvexA1.theorem_2_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:34.374126+00:00
-- url     : https://prove2.me/theorems/73c2c1c4-57a8-4329-9e61-1563ab1b3a69
-- title:
--   Theorem 2.2, p. 10 — under (C_α), ‖𝒴 − π(f)‖₂ ≤ 𝔆₁[f]₁ε, 𝔆₁ universal, at cost ≤ (5log γ₀⁻¹/2αγ₀)Υ₁²ε⁻²⌈log₂(Υ₁²ε⁻²)⌉³
-- statement:
--   There is a universal constant $\mathfrak C_1$ with the following property.
--
--   Let $b:\mathbb R^d\to\mathbb R^d$ be $L$-Lipschitz and satisfy $(\mathbf C_\alpha)$, $\langle b(y)-b(x),y-x\rangle\le-\alpha|x-y|^2$, with $\alpha\in(0,L\wedge1]$; let $\sigma>0$; let $B^{(0)},B^{(1)},\dots$ be independent standard $d$-dimensional Brownian motions; let $\pi$ be an invariant probability of the diffusion $dX_t=b(X_t)dt+\sigma dB_t$; let $f$ be Lipschitz and integrable under $\pi$; let $x_0\in\mathbb R^d$ and $\gamma_0\in(0,\frac\alpha{2L^2}\wedge\frac12]$. With $\Upsilon_1=\big(1\vee(\alpha^{-2}|b(x_0)|^2+\alpha^{-1}\sigma^2d)\big)^{1/2}$, set for $\varepsilon\in(0,1)$
--   $$r_0=\Upsilon_1,\quad R_\varepsilon=\lceil2\log_2(r_0\varepsilon^{-1})\rceil,\quad T_r=\frac{\Upsilon_1^2\log(\gamma_0^{-1})}\alpha\varepsilon^{-2}R_\varepsilon^22^{-r},\quad\tau=2\alpha^{-1}|\log\varepsilon|+\alpha^{-1}\log\Upsilon_1,$$
--   and let $\mathcal Y$ be the multilevel occupation measure (7) with these parameters, steps $\gamma_r=\gamma_02^{-r}$ and start $x_0$. If $2\log(\Upsilon_1\varepsilon^{-2})\le\log(\gamma_0^{-1})R_\varepsilon^2$ (the condition (13) defining $\varepsilon_0$), then
--   $$\big\|\mathcal Y(f)-\pi(f)\big\|_2\le\mathfrak C_1[f]_1\varepsilon\qquad\text{and}\qquad\mathcal C(\mathcal Y)\le\frac{5\log(\gamma_0^{-1})}{2\alpha\gamma_0}\Upsilon_1^2\varepsilon^{-2}R_\varepsilon^3.$$
--
--   So, under strong contractivity, the multilevel Langevin pathwise average reaches root-mean-square accuracy $\varepsilon$ at a cost of order $\varepsilon^{-2}\log^3(\varepsilon^{-1})$, with explicit polynomial dependence on the dimension through $\Upsilon_1^2$, and the step $\gamma_0$ need not depend on $d$.
--
--   **Formalization Note** (14) prints $\lceil\log_2^3(\Upsilon_1^2\varepsilon^{-2})\rceil$; its proof gives $\frac52\gamma_0^{-1}\mathfrak t\varepsilon^{-2}R_\varepsilon^3$ with $R_\varepsilon=\lceil\log_2(\Upsilon_1^2\varepsilon^{-2})\rceil$, i.e. the cube of the ceiling (as in (15)); the ceiling of the cube is false for some $\varepsilon$, since the cost equals $\frac{T_0}{\gamma_0}(1+\frac32R_\varepsilon)$. The page's $\varepsilon_0=\max\{\dots\}$ need not be well defined (the set need not be an interval); the theorem is stated for every $\varepsilon\in(0,1)$ satisfying the defining inequality (13). $\pi$ is an invariant law of the pathwise solution family driven by $B^{(0)}$; the error is `eLpNorm … 2 P` in $[0,\infty]$; the universal constant precedes every datum.
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Theorem 2.2 (first part), (9), (12)–(14), p. 10; proof §5.2, pp. 35–36

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Theorem 2.2, first part, p. 10: under (C_α), with the explicit parameters
`r₀ = Υ₁`, `R_ε = ⌈2 log₂(Υ₁/ε)⌉`, `T_r = Υ₁² log(γ₀⁻¹) α⁻¹ ε⁻² R_ε² 2^{−r}`,
`τ = 2α⁻¹|log ε| + α⁻¹ log Υ₁`, the multilevel estimator has L²-error `≤ 𝔆₁ [f]₁ ε` with a
universal `𝔆₁`, and cost `≤ (5 log(γ₀⁻¹)/(2αγ₀)) Υ₁² ε⁻² R_ε³`. -/
theorem theorem_2_2 : ∃ C₁ : ℝ,
    ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → ℝ≥0 → Ω → SDEState d) (_hB : ∀ r, IsStandardBrownian P (B r))
    (_hind : iIndepFun (fun r ω => fun t => B r t ω) P)
    (b : SDEState d → SDEState d) (L α σ : ℝ) (_hLip : ∀ x y, ‖b x - b y‖ ≤ L * ‖x - y‖)
    (_hC : CondC b α) (_hα : 0 < α) (_hαL : α ≤ L) (_hα1 : α ≤ 1) (_hσ : 0 < σ)
    (Xsol : SDEState d → ℝ≥0 → Ω → SDEState d)
    (_hX : ∀ x, IsAddSolution b σ (B 0) x (Xsol x))
    (π : Measure (SDEState d)) [IsProbabilityMeasure π] (_hπ : IsInvDiffusion P Xsol π)
    (f : SDEState d → ℝ) (_hf : ∃ K, LipschitzWith K f) (_hfπ : Integrable f π)
    (x₀ : SDEState d) (γ₀ ε : ℝ) (_hγ₀ : 0 < γ₀) (_hγ₀' : γ₀ ≤ min (α / (2 * L ^ 2)) (1 / 2))
    (_hε : 0 < ε) (_hε1 : ε < 1),
    let Υ₁ := Real.sqrt (Upsilon1Sq b σ α x₀)
    let R := MLLangevin.General.Reps Υ₁ (1 / 2) ε
    let T : ℕ → ℝ := fun r => Υ₁ ^ 2 * Real.log γ₀⁻¹ / α * ε⁻¹ ^ 2 * (R : ℝ) ^ 2 *
      (2 : ℝ) ^ (-(r : ℝ))
    let τ := 2 * α⁻¹ * |Real.log ε| + α⁻¹ * Real.log Υ₁
    2 * Real.log (Υ₁ * ε⁻¹ ^ 2) ≤ Real.log γ₀⁻¹ * (R : ℝ) ^ 2 →
    eLpNorm (fun ω => estimator b σ x₀ γ₀ R τ T B f ω - ∫ x, f x ∂π) 2 P ≤
        ENNReal.ofReal (C₁ * lipConst f * ε) ∧
      cost R γ₀ T ≤ 5 * Real.log γ₀⁻¹ / (2 * α * γ₀) * Υ₁ ^ 2 * ε⁻¹ ^ 2 * (R : ℝ) ^ 3 := by sorry

end MLLangevin.ConvexA1
