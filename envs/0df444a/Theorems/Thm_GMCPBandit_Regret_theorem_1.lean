-- Prove2me | Theorems.Thm_GMCPBandit_Regret_theorem_1
-- name    : GMCPBandit.Regret.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-13T23:33:46.940585+00:00
-- url     : https://prove2.me/theorems/386cd09c-2751-41ba-b131-2dc37bb0d227
-- title:
--   Theorem 1, p. 15 — the G-MCP-Bandit has expected cumulative regret ≤ R_max(T₀+|K|) + c·log(T+1) for T ≥ T₀
-- statement:
--   Work in the generalized linear covariate bandit of §3: $d\ge1$ covariates, $K\ge2$ decisions with sparse parameters $\beta_k$, a known reward family $g(\cdot\mid\eta)\,\nu$, and Assumptions A.1–A.5 with constants $x_{\max},s,R_{\max},\beta_{\min},b$ (A.1), $C$ (A.2), $h,p^*$ (A.3), $\kappa$ (A.4) and $\sigma,\sigma_2,\sigma_3$ (A.5).
--
--   Let $a\ge2304s/(\kappa p^*)$. Then there are constants $C_0\ge10$ and $C_4,C_5,T_0,C_\beta>0$, independent of $T$, such that the following holds. Run the G-MCP-Bandit with $t_0=2C_0|\mathcal K|$, the margin $h$ of A.3, $\lambda_{1,0}=C_5$, $\lambda_{2,0}=C_4$ and $a$. For every 2sWL selection rule, every tie-breaking rule and every $T\ge T_0$, its cumulative regret satisfies
--   $$R^C(T)\le R_{\max}(T_0+|\mathcal K|)+\Big(6R_{\max}|\mathcal K|C_0+41R_{\max}|\mathcal K|+2e^{4\sigma_2x_{\max}b}\,C\,R_{\max}^3|\mathcal K|x_{\max}^2C_\beta s^3\Big)\log(T+1).$$
--
--   This is the paper's main result: the G-MCP-Bandit attains regret of order $\log T$ in the horizon, against the $\log^2T$ of the Lasso bandit, for generalized linear rewards with high-dimensional sparse parameters.
--
--   **Formalization Note** The regret is $R^C(T)=\sum_{t=1}^T\mathbb E[\max_k\mu(x_t^\top\beta_k)-\mu(x_t^\top\beta_{\pi_t})]$, equal to the paper's $\mathbb E[R^{\pi^*_t}_t-R^{\pi_t}_t]$ by the tower property. The page writes $\lambda_1,\lambda_2$ at the horizon $T$; the algorithm box uses $\lambda_1(t),\lambda_2(t)$ at every $t$, which is what is formalized, with $\lambda_{1,0}=C_5$ and $\lambda_{2,0}=C_4$. The trailing $O(|\mathcal K|s^2(s+\log d)\log T)$ and the explicit lower bound on $T_0$ are not formalized: $T_0$ is existential (positive, as on the page) and enters the bound. The printed coefficient $2e^{4\sigma_2x_{\max}b}$ is kept although §5.4 and (EC.50) write $4e^{4\sigma^2x_{\max}b}$; $C_\beta$ is existential and absorbs the factor. The condition $a\ge2304s/(\kappa p^*)$ is kept as printed (Lemma EC.9 uses $>$). The selection and tie-breaking rules are required to be measurable, so the expectations are genuine.
-- source:
--   Wang, Wei and Yao, Online Learning and Decision-Making under Generalized Linear Model with High-Dimensional Data, arXiv:1812.02962v1, p. 15, Theorem 1

import Mathlib
import Definitions.Def_GMCPBandit_Regret_Model
import Definitions.Def_GMCPBandit_Regret_Algorithm

open MeasureTheory ProbabilityTheory

namespace GMCPBandit.Regret

universe u

/-- **Theorem 1** (p. 15). Under A.1–A.5, for every `a ≥ 2304 s/(κ p*)` there are constants
`C₀ ≥ 10`, `C₄, C₅, T₀, C_β > 0`, independent of `T`, such that the G-MCP-Bandit run with
`t₀ = 2C₀|𝒦|`, `h` (A.3), `λ_{1,0} = C₅`, `λ_{2,0} = C₄` and `a` has, for every 2sWL selection rule,
every tie-breaking rule and every `T ≥ T₀`,
`R^C(T) ≤ R_max(T₀ + |𝒦|) + (6R_max|𝒦|C₀ + 41R_max|𝒦| + 2e^{4σ₂x_max b} C R_max³ |𝒦| x_max² C_β s³) log(T+1)`. -/
theorem theorem_1 {d K : ℕ} [NeZero K] (hd : 1 ≤ d) (hK : 2 ≤ K)
    (𝒳 : Set (Fin d → ℝ)) (PX : Measure (Fin d → ℝ)) (ν : Measure ℝ) (g : ℝ → ℝ → ℝ)
    (β : Fin K → Fin d → ℝ) (xmax s Rmax βmin b C h pstar κ σ σ2 σ3 : ℝ)
    (Ko Ks : Finset (Fin K))
    (hglm : IsGLMFamily ν g Rmax)
    (hA1 : A1 𝒳 β xmax s Rmax βmin b)
    (hA2 : A2 PX ν g β Rmax C)
    (hA3 : A3 𝒳 PX ν g β Ko Ks h pstar)
    (hA4 : A4 𝒳 PX ν g β Ko h s b κ)
    (hA5 : A5 g Rmax b xmax σ σ2 σ3) :
    ∀ a : ℝ, 2304 * s / (κ * pstar) ≤ a →
    ∃ C0 C4 C5 T0 Cβ : ℝ, 10 ≤ C0 ∧ 0 < C4 ∧ 0 < C5 ∧ 0 < T0 ∧ 0 < Cβ ∧
    ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : ℕ → Ω → Fin d → ℝ) (R : ℕ → Ω → Fin K → ℝ) (V : ℕ → Ω → ℝ) (A : ℕ → Ω → Fin K),
      IsPrimitives P 𝒳 PX ν g β Rmax X R V A →
    ∀ sel : WLSelector d, IsWLSelector g Rmax b sel →
    ∀ tb : ArgmaxRule K, IsArgmaxRule tb →
    ∀ T : ℕ, T0 ≤ (T : ℝ) →
      regret P ν g β sel tb ⟨2 * C0 * K, h, C5, C4, a⟩ X R V A T ≤
        Rmax * (T0 + K) +
          (6 * Rmax * K * C0 + 41 * Rmax * K +
            2 * Real.exp (4 * σ2 * xmax * b) * C * Rmax ^ 3 * K * xmax ^ 2 * Cβ * s ^ 3) *
            Real.log ((T : ℝ) + 1) := by sorry

end GMCPBandit.Regret
