-- Prove2me | Theorems.Thm_MFIrrev_Equilibrium_theorem_4_1
-- name    : MFIrrev.Equilibrium.theorem_4_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:20.391901+00:00
-- url     : https://prove2.me/theorems/8a482ccd-7aa9-4b2b-85d0-c1e876ade474
-- title:
--   Theorem 4.1, p. 23 — a unique stationary mean-field equilibrium exists, and its investment strategy is the barrier control (4.11)
-- statement:
--   Assume the standing conditions of §2: $\delta,\sigma_1,\sigma_2,\rho,c,\kappa>0$, $p_1,p_2\in(0,1)$, $\varphi_i,\zeta_i>0$, $0<\alpha<1$, $\min_i\varphi_i>\rho+\delta$; Assumption 2.1, $\rho>2\max\{\sigma_1^2,\sigma_2^2\}$; and $1+\theta_2<0$, where $\theta_2$ is the largest negative root of $\bar\phi(\theta)=\phi_1(\theta)\phi_2(\theta)-p_1p_2$ with $\phi_i(\theta)=\frac12\sigma_i^2\theta^2+(\delta+\frac12\sigma_i^2)\theta-p_i$. Assume also $(\rho+\delta)\kappa<\varphi_i$ for $i=1,2$.
--
--   Then for every initial state $(x,i)$ with $x>0$ there exist barriers $a^\star_1,a^\star_2>0$ and $Q^\star\in(0,\infty)^2$ such that, with $I^\star$ the barrier control
--   $$I^\star_t=0\vee\sup_{0\le s\le t}\Big(\ln\big(a^\star_{\varepsilon_s}/x\big)+\int_0^s\big(\delta+\tfrac12\sigma^2_{\varepsilon_u}\big)du-\int_0^s\sigma_{\varepsilon_u}dB_u\Big),\qquad I^\star_{0-}=0,$$
--   the pair $(I^\star,Q^\star)$ is a stationary mean-field equilibrium in the sense of Definition 2.2, and it is the unique one: every stationary mean-field equilibrium $(I,Q)$ has $Q=Q^\star$ and $I$ indistinguishable from $I^\star$ under $\mathbb P(\cdot\mid\varepsilon_0=i)$.
--
--   This is the paper's main result: the mean-field consistency $Q^\star_i=\pi_i^{-1}\int_0^\infty x\,p_\infty(dx,i)$ (system (4.37)) has exactly one solution, and the equilibrium firm invests minimally so as to keep its capacity above a regime-dependent barrier.
--
--   **Formalization Note.** Regimes are `Fin 2` (index `0` = regime 1). "$1+\theta_2<0$" is stated as "$\bar\phi$ has no root in $[-1,0)$", which is equivalent because the negative roots of $\bar\phi$ are $\theta_1<\theta_2<0$; this avoids defining $\theta_2$ by a supremum. The first claim of Theorem 4.1 (a unique solution of (4.37)) is contained in the statement: for each solution $Q$ of (4.37) the pair $(I^\star(Q),Q)$ is an equilibrium, so uniqueness of equilibria gives uniqueness of $Q$. The barrier form is Theorem 2.4(i). The hypothesis $(\rho+\delta)\kappa<\varphi_i$ is added: the proof's Step 3 drops $\kappa$ in an integration by parts, and once restored, the lower bound on the barriers needs it (footnote 1 calls $\rho+\delta$ the competitive price, which is $(\rho+\delta)\kappa$ for marginal cost $\kappa$); it coincides with the printed $\min_i\varphi_i>\rho+\delta$ when $\kappa=1$. Uniqueness is stated as printed (the pair, with the control unique up to indistinguishability). The stationary distribution is the weak-limit reading of the `Model` definition, and $Q^\star\in(0,\infty)^2$ because $\eta$ is infinite at $Q_i=0$.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, p. 23, Theorem 4.1 (informal version Theorem 2.4, p. 7, including (i)); proof pp. 23–25

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_Model

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MFIrrev.Equilibrium

/-- Theorem 4.1 (with the barrier form of Theorem 2.4(i)), Aïd–Basei–Ferrari p. 23. Regime index `0`
is the paper's regime 1. Under the standing assumptions, Assumption 2.1 and `1 + θ₂ < 0` (no root of
`ϕ̄` in `[−1, 0)`), and the disclosed pin `(ρ+δ)κ < φ_j`: for every initial state `(x, i)` there are
positive barriers `a⋆` and `Q⋆ ∈ (0, ∞)²` such that `(I⋆, Q⋆)`, with `I⋆` the barrier control (4.11)
at `a⋆`, is a stationary mean-field equilibrium (Definition 2.2), and it is the unique one: every
equilibrium `(I, Q)` has `Q = Q⋆` and `I` indistinguishable from `I⋆` under `P_(x,i)`. -/
theorem theorem_4_1 (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j) (hp : ∀ j, 0 < m.p j ∧ m.p j < 1)
    (hρ : 0 < m.ρ) (hc : 0 < m.c) (hκ : 0 < m.κ) (hφ : ∀ j, 0 < m.φ j) (hζ : ∀ j, 0 < m.ζ j)
    (hα0 : 0 < m.α) (hα1 : m.α < 1) (hφρδ : ∀ j, m.ρ + m.δ < m.φ j)
    (hA21 : 2 * max (m.σ 0 ^ 2) (m.σ 1 ^ 2) < m.ρ)
    (hθ : ∀ θ : ℝ, -1 ≤ θ → θ < 0 → phiBar m θ ≠ 0)
    (hpin : ∀ j, (m.ρ + m.δ) * m.κ < m.φ j)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Setting Ω) (hS : IsSetting m P S)
    (x : ℝ) (hx : 0 < x) (i : Fin 2) :
    ∃ a Q : Fin 2 → ℝ, (∀ j, 0 < a j) ∧ IsMFE m P S x i (barrier m S a x) Q ∧
      ∀ (I : ℝ≥0 → Ω → ℝ) (Q' : Fin 2 → ℝ), IsMFE m P S x i I Q' →
        Q' = Q ∧ ∀ᵐ ω ∂(Pcond P S i), ∀ t, I t ω = barrier m S a x t ω := by sorry

end MFIrrev.Equilibrium
