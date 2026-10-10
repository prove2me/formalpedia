-- Prove2me | Theorems.Thm_LQGMapII_Kolmogorov_proposition_2_3
-- name    : LQGMapII.Kolmogorov.proposition_2_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T14:41:32.281372+00:00
-- url     : https://prove2.me/theorems/5f1a186d-385e-47f6-89c7-e4a7b7f53a18
-- title:
--   Proposition 2.3, p. 30 — a Hölder modification for every γ < β/α, with P[M ≥ t] ≤ c₁t^{−α} for its Hölder norm
-- statement:
--   **Quantitative Kolmogorov–Čentsov criterion.** Fix $d \in \mathbb N$ and constants $\alpha, \beta, c_0 > 0$. For each $\gamma \in (0, \beta/\alpha)$ there is a constant $c_1(\gamma) > 0$, depending only on $d, \alpha, \beta, \gamma, c_0$, with the following property.
--
--   Let $(X_u)_{u \in [0,1]^d}$ be any real random field on a probability space $(\Omega, \mathcal F, \mathbf P)$ such that for all $u, v \in [0,1]^d$
--   $$
--   \mathbf E\big[|X_u - X_v|^\alpha\big] \le c_0 |u - v|^{d+\beta}. \qquad (2.6)
--   $$
--   Then there is a modification $Y$ of $X$ ($Y_u = X_u$ almost surely for every $u$) such that for every $\gamma \in (0, \beta/\alpha)$:
--
--   1. for every $\omega$ there is $M > 0$ with $|Y_u(\omega) - Y_v(\omega)| \le M |u - v|^\gamma$ for all $u, v \in [0,1]^d$ (this is (2.7));
--   2. the $\gamma$-Hölder norm $M_\gamma(\omega) = \sup_{u \ne v} |Y_u(\omega) - Y_v(\omega)| / |u - v|^\gamma$ satisfies
--   $$
--   \mathbf P\big[M_\gamma \ge t\big] \le c_1(\gamma)\, t^{-\alpha} \quad \text{for all } t \ge 1. \qquad (2.8)
--   $$
--
--   The first statement is the classical criterion; the second gives a polynomial tail for the random Hölder constant whose constant does not depend on the field, only on the parameters in (2.6). The paper applies it to the circle-average process of the Gaussian free field.
--
--   **Formalization Note** (2.6) is `IsKolmogorovProcess X P α (d + β) c₀`: the lower Lebesgue integral of $|X_u - X_v|^\alpha$ in $[0,\infty]$, with each pair $(X_u, X_v)$ Borel measurable (the paper's "random field"); $|u - v|$ is the Euclidean distance on $[0,1]^d$. The constant $c_1$ is a function of $\gamma$ chosen before the probability space and the field, which makes it uniform over all fields with the same $\alpha, \beta, c_0$ (the paper lists $\alpha, \beta, \gamma, c_0$; it may also depend on the fixed dimension $d$); the probability space lives in `Type`. The modification is chosen before $\gamma$. $M_\gamma$ is Mathlib's `eHolderNorm γ`, the least Hölder constant, valued in $[0,\infty]$, so it is never a junk $0$. (2.7) is stated for every $\omega$. If the event $\{M_\gamma \ge t\}$ is not measurable, $\mathbf P$ is the outer measure.
-- source:
--   Miller, Sheffield, Liouville quantum gravity and the Brownian map II, Ann. Probab. (2021), DOI 10.1214/21-AOP1506, accepted manuscript, Proposition 2.3, (2.6)–(2.8), p. 30

import Mathlib
import Definitions.Def_LQGMapII_Kolmogorov_Setting

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace LQGMapII.Kolmogorov

/-- Proposition 2.3, (2.6)–(2.8), p. 30 (quantitative Kolmogorov–Čentsov): under (2.6) there is
one modification `Y` of `X` that is `γ`-Hölder for every `γ ∈ (0, β/α)`, and its `γ`-Hölder norm
`M = sup_{u ≠ v} |Y_u - Y_v| / |u - v|^γ` satisfies `P[M ≥ t] ≤ c₁ t^{-α}` for all `t ≥ 1`,
where `c₁ > 0` depends only on `d, α, β, γ, c₀` (it is chosen before the field). -/
theorem proposition_2_3 (d : ℕ) (α β : ℝ) (c₀ : ℝ≥0) (hα : 0 < α) (hβ : 0 < β) (hc₀ : 0 < c₀) :
    ∃ c₁ : ℝ≥0 → ℝ≥0, (∀ γ, 0 < c₁ γ) ∧
      ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X : Cube d → Ω → ℝ), IsKolmogorovProcess X P α ((d : ℝ) + β) c₀ →
        ∃ Y : Cube d → Ω → ℝ, (∀ u, Y u =ᵐ[P] X u) ∧
          ∀ γ : ℝ≥0, 0 < γ → (γ : ℝ) < β / α →
            (∀ ω, ∃ M : ℝ≥0, 0 < M ∧ HolderWith M γ (fun u ↦ Y u ω)) ∧
            ∀ t : ℝ, 1 ≤ t →
              P {ω | ENNReal.ofReal t ≤ eHolderNorm γ (fun u ↦ Y u ω)} ≤
                ENNReal.ofReal ((c₁ γ : ℝ) * t ^ (-α)) := by sorry

end LQGMapII.Kolmogorov
