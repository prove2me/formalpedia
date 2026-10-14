-- Prove2me | Theorems.Thm_MFIrrev_Equilibrium_corollary_4_7
-- name    : MFIrrev.Equilibrium.corollary_4_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:12.271926+00:00
-- url     : https://prove2.me/theorems/5e25e683-c285-4082-ba40-efdf8c2d6949
-- title:
--   Corollary 4.7, pp. 22–23 — if 1 + θ₂ < 0, the regime-wise stationary means ∫ x p∞(dx, i) are given by (4.35) and (4.36)
-- statement:
--   In the setting of Proposition 4.6 (barriers $0<a_1<a_2$, negative roots $\theta_1<\theta_2<0$ of $\bar\phi$, the unique solution $(A_1,A_2,B_1,B_2)$ of (4.31), $\phi_{1i}=\phi_1(\theta_i)/p_2$), assume moreover $1+\theta_2<0$. Then for every stationary distribution $p_\infty$ of the barrier-controlled process $(X^{I^\star}_t,\varepsilon_t)$ the regime-wise first moments are finite and
--   $$\int_0^\infty x\,p_\infty(dx,1)=\frac{A_1\alpha_1^+a_1}{1+\alpha_1^+}\Big[\Big(\frac{a_2}{a_1}\Big)^{1+\alpha_1^+}-1\Big]+\frac{A_2\alpha_1^-a_1}{1+\alpha_1^-}\Big[\Big(\frac{a_2}{a_1}\Big)^{1+\alpha_1^-}-1\Big]-\frac{B_1\theta_1a_2}{1+\theta_1}-\frac{B_2\theta_2a_2}{1+\theta_2},$$
--   $$\int_0^\infty x\,p_\infty(dx,2)=\Big[\frac{B_1\theta_1\phi_{11}}{1+\theta_1}+\frac{B_2\theta_2\phi_{12}}{1+\theta_2}\Big]a_2.$$
--
--   These are the two components of the map $Q\mapsto\mathcal RQ$ (after division by $\pi_i$) whose fixed point is the equilibrium.
--
--   **Formalization Note.** Regimes are `Fin 2`: regime 1 is index `0` ((4.35)) and regime 2 is index `1` ((4.36)). The integrals are over $\mathbb R\times\{1,2\}$ of $x\mathbb 1_{\{\text{regime}=j\}}$; a stationary distribution has no mass on $x\le0$, so they equal the page's $\int_0^\infty$. No denominator vanishes: $1+\theta_1<1+\theta_2<0$, $1+\alpha_1^-<0$ because $\alpha_1^-<\theta_2$, and $1+\alpha_1^+>0$. (4.34) is Proposition 4.6 after the change of variables $z=\ln x$ and is not posed again.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, pp. 22–23, Corollary 4.7, (4.35)–(4.36)

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_Model

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MFIrrev.Equilibrium

/-- Corollary 4.7, (4.35)–(4.36), Aïd–Basei–Ferrari pp. 22–23. Regime index `0` is the paper's regime 1.
In the setting of Proposition 4.6, if moreover `1 + θ₂ < 0`, then under every stationary
distribution `μ` of the barrier-controlled process the regime-wise first moments are finite and
`∫ x p∞(dx, 1)`, `∫ x p∞(dx, 2)` are given by (4.35) and (4.36). -/
theorem corollary_4_7 (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j) (hp : ∀ j, 0 < m.p j ∧ m.p j < 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Setting Ω) (hS : IsSetting m P S)
    (a : Fin 2 → ℝ) (ha0 : 0 < a 0) (ha01 : a 0 < a 1)
    (θ1 θ2 : ℝ) (hθ12 : θ1 < θ2) (hθ2 : θ2 < 0) (hroot1 : phiBar m θ1 = 0) (hroot2 : phiBar m θ2 = 0)
    (A1 A2 B1 B2 : ℝ)
    (hsys : Sys431 m (Real.log (a 0)) (Real.log (a 1)) θ1 θ2 A1 A2 B1 B2)
    (hsys_unique : ∀ A1' A2' B1' B2' : ℝ,
      Sys431 m (Real.log (a 0)) (Real.log (a 1)) θ1 θ2 A1' A2' B1' B2' →
        A1' = A1 ∧ A2' = A2 ∧ B1' = B1 ∧ B2' = B2)
    (x : ℝ) (hx : 0 < x) (i : Fin 2)
    (h1θ2 : 1 + θ2 < 0) :
    ∀ μ : Measure (ℝ × Fin 2), HasLimitLaw m P S x i (barrier m S a x) μ →
      (∀ j : Fin 2, Integrable (fun z : ℝ × Fin 2 => if z.2 = j then z.1 else 0) μ) ∧
      ∫ z, (if z.2 = 0 then z.1 else 0) ∂μ =
        A1 * alphaPlus m * a 0 / (1 + alphaPlus m) * ((a 1 / a 0) ^ (1 + alphaPlus m) - 1)
        + A2 * alphaMinus m * a 0 / (1 + alphaMinus m) * ((a 1 / a 0) ^ (1 + alphaMinus m) - 1)
        - B1 * θ1 * a 1 / (1 + θ1) - B2 * θ2 * a 1 / (1 + θ2) ∧
      ∫ z, (if z.2 = 1 then z.1 else 0) ∂μ =
        (B1 * θ1 * phi1i m θ1 / (1 + θ1) + B2 * θ2 * phi1i m θ2 / (1 + θ2)) * a 1 := by sorry

end MFIrrev.Equilibrium
