-- Prove2me | Theorems.Thm_MLLangevin_ConvexA1_remark_4_1
-- name    : MLLangevin.ConvexA1.remark_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:27:34.900055+00:00
-- url     : https://prove2.me/theorems/bd32aa5f-78b3-4be9-8475-37843bb6d53d
-- title:
--   Remark 4.1, pp. 27–28 — Theorem 2.1 (ii) for the additive scheme, with c₂, c₃, c₄ known up to a factor κ
-- statement:
--   Fix $\kappa\ge1$. There is a constant $\tilde{\mathfrak C}_1$, depending only on $\kappa$, such that the following holds.
--
--   Consider the additive Euler schemes built from a Lipschitz drift $b$ and a noise level $\sigma>0$, driven by independent standard $d$-dimensional Brownian motions $B^{(0)},B^{(1)},\dots$, one per level. Let $f$ be Lipschitz, $\pi$ a probability with $f\in L^1(\pi)$, $\alpha\in(0,1]$, $\mathfrak a\in[1,2]$, $\delta\in[\frac12,1]$ if $\mathfrak a=1$ and $\delta\in(\frac{1+\mathfrak a}4,1]$ if $\mathfrak a>1$, $\eta_0\in(0,\frac12]$, and assume every step $\gamma\in(0,\eta_0]$ has an invariant probability. Assume $(\mathbf H_1)$, $(\mathbf H_2)$, $(\mathbf H_4)$ for every level's Brownian motion and $(\mathbf H_3)$, with constants $c_1(\cdot),c_2,c_3,c_4$. Let $\tilde c_2,\tilde c_3,\tilde c_4$ satisfy $c_i\le\kappa\tilde c_i$ and $\tilde c_4>0$, and choose
--   $$\gamma_0\in(0,\eta_0],\quad\tilde r_0\ge1\vee(\tilde c_3\gamma_0^\delta),\quad\tilde{\mathfrak t}\ge\frac{\mathfrak d_{\mathfrak a}}\alpha\max\big(\tilde c_2^2\gamma_0^{\mathfrak a}\log(\gamma_0^{-1}),\tilde c_4^2\big),$$
--   $\tilde R_\varepsilon=\lceil\delta^{-1}\log_2(\tilde r_0\varepsilon^{-1})\rceil$ and $\tilde T_r$ by (8) with $\tilde{\mathfrak t}$. For every $\varepsilon\in(0,1)$ and every $\tau$ with $\tau_1|\log\varepsilon|+\tilde\tau_2\le\tau\le\frac12\tilde T_{\tilde R_\varepsilon}$, where $\tau_1=\frac{1+\mathfrak a-2\delta}{\alpha\delta}$ and $\tilde\tau_2=0\vee\frac1\alpha\log\big(\tilde r_0^{\frac{1+\mathfrak a}{2\delta}}(\mathfrak d_{\mathfrak a}\tilde c_4)^{-1}\big)$,
--   $$\big\|\mathcal Y(f)-\pi(f)\big\|_2\le\tilde{\mathfrak C}_1[f]_1\varepsilon,\qquad\mathcal C(\mathcal Y)\le\mathfrak c_{\mathfrak a}\gamma_0^{-1}\tilde{\mathfrak t}\cdot\begin{cases}\varepsilon^{-2}&\mathfrak a>1,\\\varepsilon^{-2}\tilde R_\varepsilon^3&\mathfrak a=1.\end{cases}$$
--
--   This is how Theorem 2.1 (ii) is applied when the constants of $(\mathbf H_2)$–$(\mathbf H_4)$ are known only up to universal factors, as in Proposition 2.1.
--
--   **Formalization Note** The page's "$\tilde c_i=\lambda_ic_i$ with universal $\lambda_i$" is read one-sidedly, $c_i\le\kappa\tilde c_i$, with the error constant depending only on $\kappa$; this is the form §5.2 feeds in. The theorem is stated for the additive scheme of this mission; $\pi$ is any probability satisfying $(\mathbf H_3)$ (in particular the diffusion's invariant law), since the proof uses $\pi$ only through $(\mathbf H_3)$. Existence of an invariant probability for each step is the paper's standing assumption (p. 6). $\tilde c_4>0$ excludes the case where the page's $\tilde\tau_2$ is $+\infty$. The page's $\varepsilon_0$ is replaced by quantifying over every $\varepsilon\in(0,1)$ for which the $\tau$-interval is used. The cost is the formula of p. 6.
-- source:
--   Egéa–Panloup, Multilevel-Langevin pathwise average for Gibbs approximation, arXiv:2109.07753v2, Remark 4.1, pp. 27–28, with Theorem 2.1 (ii), pp. 7–8, (8), p. 7, and (39)–(40), p. 26

import Mathlib
import Definitions.Def_MLLangevin_ConvexA1_Setting

namespace MLLangevin.ConvexA1

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

/-- Remark 4.1, pp. 27–28 (Theorem 2.1 (ii) with constants known up to universal factors), for
the additive Euler scheme: if the algorithm is built with `c̃₂, c̃₃, c̃₄` such that the true
constants satisfy `c_i ≤ κ c̃_i`, then (9) holds with a constant depending only on `κ` and
(10) holds with `𝔆̃₂ = 𝔠_𝔞 γ₀⁻¹ 𝔱̃`. -/
theorem remark_4_1 : ∀ κ : ℝ, 1 ≤ κ → ∃ C₁ : ℝ,
    ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (B : ℕ → ℝ≥0 → Ω → SDEState d) (_hB : ∀ r, IsStandardBrownian P (B r))
    (_hind : iIndepFun (fun r ω => fun t => B r t ω) P)
    (b : SDEState d → SDEState d) (_hb : ∃ K, LipschitzWith K b) (σ : ℝ) (_hσ : 0 < σ)
    (f : SDEState d → ℝ) (_hf : ∃ K, LipschitzWith K f)
    (π : Measure (SDEState d)) [IsProbabilityMeasure π] (_hfπ : Integrable f π)
    (α 𝔞 δ η₀ : ℝ) (x₀ : SDEState d) (c₁ : SDEState d → ℝ) (c₂ c₃ c₄ c₂' c₃' c₄' : ℝ)
    (γ₀ r₀ 𝔱 ε τ : ℝ),
    0 < α → α ≤ 1 → 1 ≤ 𝔞 → 𝔞 ≤ 2 →
    (𝔞 = 1 → 1 / 2 ≤ δ ∧ δ ≤ 1) → (1 < 𝔞 → (1 + 𝔞) / 4 < δ ∧ δ ≤ 1) →
    0 < η₀ → η₀ ≤ 1 / 2 →
    (∀ γ : ℝ, 0 < γ → γ ≤ η₀ →
      ∃ πγ : Measure (SDEState d), IsProbabilityMeasure πγ ∧ IsInvChain P b σ γ (B 0) πγ) →
    (∀ r, H1 P b σ (B r) f α η₀ c₁) → (∀ r, H2 P b σ (B r) x₀ η₀ 𝔞 c₂) →
    H3 P b σ (B 0) f π η₀ δ c₃ → (∀ r, H4 P b σ (B r) x₀ η₀ c₁ c₄) →
    c₂ ≤ κ * c₂' → c₃ ≤ κ * c₃' → c₄ ≤ κ * c₄' → 0 < c₄' →
    0 < γ₀ → γ₀ ≤ η₀ → max 1 (c₃' * γ₀ ^ δ) ≤ r₀ →
    MLLangevin.General.da 𝔞 / α * max (c₂' ^ 2 * γ₀ ^ 𝔞 * Real.log γ₀⁻¹) (c₄' ^ 2) ≤ 𝔱 →
    0 < ε → ε < 1 →
    tau1 𝔞 δ α * |Real.log ε| + tau2 𝔞 δ α r₀ c₄' ≤ τ →
    τ ≤ MLLangevin.General.Tsched 𝔞 𝔱 ε (MLLangevin.General.Reps r₀ δ ε) (MLLangevin.General.Reps r₀ δ ε) / 2 →
    eLpNorm (fun ω => estimator b σ x₀ γ₀ (MLLangevin.General.Reps r₀ δ ε) τ
        (MLLangevin.General.Tsched 𝔞 𝔱 ε (MLLangevin.General.Reps r₀ δ ε)) B f ω - ∫ x, f x ∂π) 2 P ≤
      ENNReal.ofReal (C₁ * lipConst f * ε) ∧
    cost (MLLangevin.General.Reps r₀ δ ε) γ₀ (MLLangevin.General.Tsched 𝔞 𝔱 ε (MLLangevin.General.Reps r₀ δ ε)) ≤
      ca 𝔞 * γ₀⁻¹ * 𝔱 * (if 1 < 𝔞 then ε⁻¹ ^ 2 else ε⁻¹ ^ 2 * (MLLangevin.General.Reps r₀ δ ε : ℝ) ^ 3) := by sorry

end MLLangevin.ConvexA1
