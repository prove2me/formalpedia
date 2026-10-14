-- Prove2me | Theorems.Thm_MLLangevin_ConvexA2_remark_4_1
-- name    : MLLangevin.ConvexA2.remark_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:32:26.287382+00:00
-- url     : https://prove2.me/theorems/1dae4380-6ea5-480c-b061-fd3ef2473714
-- title:
--   Remark 4.1, pp. 27–28 — Theorem 2.1 (ii) with c̃ᵢ known up to universal factors: (9) with a universal 𝔆̃₁ and cost 𝔠_𝔞γ₀⁻¹𝔱̃ε⁻² (ε⁻²R³ if 𝔞 = 1)
-- statement:
--   For every $\kappa\ge1$ there is a constant $\tilde{\mathfrak C}_1$, depending only on $\kappa$, such that the following holds for the additive Euler scheme. Let $B^{(0)},B^{(1)},\dots$ be independent standard $d$-dimensional Brownian motions, $b$ Lipschitz, $\sigma\in\mathbb R$, $f$ Lipschitz, $\pi$ a probability measure with $f\in L^1(\pi)$, $\alpha\in(0,1]$, $\mathfrak a\in[1,2]$, $\delta\in[\frac12,1]$ if $\mathfrak a=1$ and $\delta\in(\frac{1+\mathfrak a}4,1]$ if $\mathfrak a>1$, $\eta_0\in(0,\frac12]$, $x_0\in\mathbb R^d$. Assume $(\mathbf H_1)$–$(\mathbf H_4)$ with constants $c_1(\cdot),c_2,c_3,c_4$. Let $\tilde c_2,\tilde c_3,\tilde c_4>0$ with $c_i\le\kappa\tilde c_i$, let $\gamma_0\in(0,\eta_0]$ and
--   $$\tilde r_0\ge1\vee(\tilde c_3\gamma_0^\delta),\quad\tilde R_\varepsilon=\lceil\delta^{-1}\log_2(\tilde r_0\varepsilon^{-1})\rceil,\quad\tilde{\mathfrak t}\ge\frac{\mathfrak d_{\mathfrak a}}{\alpha}\max\big(\tilde c_2^2\gamma_0^{\mathfrak a}\log(\gamma_0^{-1}),\tilde c_4^2\big),$$
--   $T_r$ as in (8) with $\tilde{\mathfrak t}$, $\tilde R_\varepsilon$, and $\gamma_r=\gamma_02^{-r}$. Let $\varepsilon\in(0,1)$ and $\tau\in[\tau_1|\log\varepsilon|+\tilde\tau_2,\frac12T_{\tilde R_\varepsilon}]$, where $\tau_1=\frac{1+\mathfrak a-2\delta}{\alpha\delta}$ and $\tilde\tau_2=0\vee\frac1\alpha\log\big(\tilde r_0^{\frac{1+\mathfrak a}{2\delta}}(\mathfrak d_{\mathfrak a}\tilde c_4)^{-1}\big)$. Then
--   $$\big\|\mathcal Y(\tilde R_\varepsilon,(\gamma_r)_r,\tau,(T_r)_r,f)-\pi(f)\big\|_2\le\tilde{\mathfrak C}_1[f]_1\varepsilon,\qquad\mathcal C(\mathcal Y)\le\mathfrak c_{\mathfrak a}\gamma_0^{-1}\tilde{\mathfrak t}\cdot\begin{cases}\varepsilon^{-2}&\mathfrak a>1,\\ \varepsilon^{-2}\tilde R_\varepsilon^3&\mathfrak a=1.\end{cases}$$
--
--   This is the form of the paper's general complexity theorem that its applications use: the constants of $(\mathbf H_2)$–$(\mathbf H_4)$ are only known up to universal factors, and the algorithm is tuned with the known upper bounds.
--
--   **Formalization Note** "We will build our algorithm with $\tilde c_i=\lambda_ic_i$, $\lambda_i$ universal" is read one-sidedly: the true constants are at most $\kappa$ times the ones used to tune the algorithm, and the constant $\tilde{\mathfrak C}_1$ depends on $\kappa$ only; this is the form in which §5.2 applies the remark. $\pi$ is any probability measure satisfying $(\mathbf H_3)$, in particular the invariant distribution of the diffusion; $\pi^\gamma$ ranges over the invariant probabilities of the chain inside $(\mathbf H_1)$ and $(\mathbf H_3)$. The paper's $\varepsilon\in(0,\varepsilon_0)$ is replaced by $\varepsilon\in(0,1)$ together with the explicit constraint $\tau\le\frac12T_{\tilde R_\varepsilon}$, which is the only role of $\varepsilon_0$. The positivity $\tilde c_i>0$ is the paper's ($\lambda_i$ positive).
-- source:
--   Egéa–Panloup, arXiv:2109.07753v2, Remark 4.1, pp. 27–28, with Theorem 2.1 (ii), pp. 7–8, (8), p. 7, and (39)–(40), p. 26

import Mathlib
import Definitions.Def_MLLangevin_ConvexA2_Multilevel
import Definitions.Def_MLLangevin_ConvexA2_DriftNorms

open MeasureTheory ProbabilityTheory EthierKurtz
open scoped ENNReal NNReal

namespace MLLangevin.ConvexA2

theorem remark_4_1 :
    ∀ κ : ℝ, 1 ≤ κ → ∃ C₁ : ℝ,
      ∀ {d : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (B : ℕ → ℝ≥0 → Ω → SDEState d), (∀ r, IsStandardBrownian P (B r)) →
      iIndepFun (fun r ω => fun t => B r t ω) P →
      ∀ (b : SDEState d → SDEState d) (σ : ℝ), (∃ K, LipschitzWith K b) →
      ∀ f : SDEState d → ℝ, (∃ K, LipschitzWith K f) →
      ∀ π : Measure (SDEState d), IsProbabilityMeasure π → Integrable f π →
      ∀ (α 𝔞 δ η₀ : ℝ) (x₀ : SDEState d) (c₁ : SDEState d → ℝ) (c₂ c₃ c₄ : ℝ),
      0 < α → α ≤ 1 → 1 ≤ 𝔞 → 𝔞 ≤ 2 →
      (𝔞 = 1 → 1 / 2 ≤ δ) → (1 < 𝔞 → (1 + 𝔞) / 4 < δ) → δ ≤ 1 →
      0 < η₀ → η₀ ≤ 1 / 2 →
      H1 P b σ B f α η₀ c₁ → H2 P b σ B x₀ η₀ 𝔞 c₂ → H3 b σ f π η₀ δ c₃ →
      H4 P b σ B x₀ η₀ c₁ c₄ →
      ∀ (c₂' c₃' c₄' γ₀ r₀ t ε τ : ℝ),
      0 < c₂' → 0 < c₃' → 0 < c₄' → c₂ ≤ κ * c₂' → c₃ ≤ κ * c₃' → c₄ ≤ κ * c₄' →
      0 < γ₀ → γ₀ ≤ η₀ → max 1 (c₃' * γ₀ ^ δ) ≤ r₀ →
      MLLangevin.General.da 𝔞 / α * max (c₂' ^ 2 * γ₀ ^ 𝔞 * Real.log γ₀⁻¹) (c₄' ^ 2) ≤ t →
      0 < ε → ε < 1 →
      tau1 𝔞 δ α * |Real.log ε| + MLLangevin.ConvexA1.tau2 𝔞 δ α r₀ c₄' ≤ τ →
      τ ≤ MLLangevin.General.Tsched 𝔞 t ε (MLLangevin.General.Reps r₀ δ ε) (MLLangevin.General.Reps r₀ δ ε) / 2 →
      eLpNorm (fun ω => estimator b σ x₀ γ₀ (MLLangevin.General.Reps r₀ δ ε) τ (MLLangevin.General.Tsched 𝔞 t ε (MLLangevin.General.Reps r₀ δ ε)) B f ω
          - ∫ x, f x ∂π) 2 P ≤ ENNReal.ofReal (C₁ * MLLangevin.ConvexA1.lipConst f * ε) ∧
      cost (MLLangevin.General.Reps r₀ δ ε) γ₀ (MLLangevin.General.Tsched 𝔞 t ε (MLLangevin.General.Reps r₀ δ ε))
        ≤ ca 𝔞 * γ₀⁻¹ * t * (if 1 < 𝔞 then ε⁻¹ ^ 2 else ε⁻¹ ^ 2 * (MLLangevin.General.Reps r₀ δ ε : ℝ) ^ 3) := by sorry

end MLLangevin.ConvexA2
