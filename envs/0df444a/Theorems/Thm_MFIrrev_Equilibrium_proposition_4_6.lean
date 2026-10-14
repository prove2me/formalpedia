-- Prove2me | Theorems.Thm_MFIrrev_Equilibrium_proposition_4_6
-- name    : MFIrrev.Equilibrium.proposition_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:26:26.303396+00:00
-- url     : https://prove2.me/theorems/a908700d-0a3f-4515-b9bd-2fa87102e22a
-- title:
--   Proposition 4.6, p. 22 — the capacity reflected at barriers 0 < a₁ < a₂ has stationary CDF Π̂(x, i) = Π(ln x, i) of (4.32)–(4.33)
-- statement:
--   Let $\delta>0$, $\sigma_1,\sigma_2>0$, $p_1,p_2\in(0,1)$, and let $0<a_1<a_2$ be barriers with $b_i=\ln a_i$ (4.25). Let $\theta_1<\theta_2<0$ be the two negative roots of $\bar\phi$ (4.29), and let $(A_1,A_2,B_1,B_2)$ be the unique solution of the linear system (4.31). Let $I^\star$ be the barrier control (4.11) at $(a_1,a_2)$ started from $x>0$ in regime $i$, and $Z_t=\ln X^{I^\star}_t$.
--
--   Then $(X^{I^\star}_t,\varepsilon_t)_{t\ge0}$ has a stationary distribution $p_\infty$ whose joint distribution function is
--   $$\widehat\Pi(x,j):=p_\infty\big((-\infty,x]\times\{j\}\big)=\Pi(\ln x,j),\qquad x>0,\ j\in\{1,2\},$$
--   with $\Pi$ the explicit function of (4.32), and $p_\infty$ puts no mass on $(-\infty,0]$. Equivalently, the stationary CDF of $(Z_t,\varepsilon_t)$ is $\Pi$.
--
--   This closed form is what makes the mean-field consistency condition of Definition 2.2 explicit.
--
--   **Formalization Note.** Regimes are `Fin 2` (index `0` = regime 1; so "$\pi_1$" is `piStat m 0`). "Stationary distribution" is read as the weak limit of the laws of $(X^{I^\star}_t,\varepsilon_t)$ under $\mathbb P(\cdot\mid\varepsilon_0=i)$, as in the `Model` definition. The case $a_1<a_2$ is the one §4.2 treats (the WLOG (4.20) with $b_1<b_2$). The roots $\theta_1,\theta_2$ enter as numbers with their defining properties, and "the unique solution" of (4.31) as a solution together with uniqueness. Only the closed form (4.32) is used; the ODE system on p. 21 is not encoded.
-- source:
--   Aïd, Basei & Ferrari, A Stationary Mean-Field Equilibrium Model of Irreversible Investment in a Two-Regime Economy, arXiv:2305.00541v1, p. 22, Proposition 4.6, (4.31)–(4.33); proof in Appendix A

import Mathlib
import Definitions.Def_MFIrrev_Equilibrium_Model

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology

namespace MFIrrev.Equilibrium

/-- Proposition 4.6, Aïd–Basei–Ferrari p. 22. Regime index `0` is the paper's regime 1. For barriers
`0 < a₁ < a₂` (log-barriers `b_i = ln a_i`), the two negative roots `θ₁ < θ₂ < 0` of (4.29) and the
unique solution `(A₁, A₂, B₁, B₂)` of (4.31), the process `(X^{I⋆}_t, ε_t)` controlled by the barrier
control (4.11) has a stationary distribution `μ` whose joint CDF is `Π(ln x, j)` of (4.32), i.e.
`Π̂(x, j)` of (4.33), and which puts no mass on `x ≤ 0`. -/
theorem proposition_4_6 (m : Params) (hδ : 0 < m.δ) (hσ : ∀ j, 0 < m.σ j) (hp : ∀ j, 0 < m.p j ∧ m.p j < 1)
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (S : Setting Ω) (hS : IsSetting m P S)
    (a : Fin 2 → ℝ) (ha0 : 0 < a 0) (ha01 : a 0 < a 1)
    (θ1 θ2 : ℝ) (hθ12 : θ1 < θ2) (hθ2 : θ2 < 0) (hroot1 : phiBar m θ1 = 0) (hroot2 : phiBar m θ2 = 0)
    (A1 A2 B1 B2 : ℝ)
    (hsys : Sys431 m (Real.log (a 0)) (Real.log (a 1)) θ1 θ2 A1 A2 B1 B2)
    (hsys_unique : ∀ A1' A2' B1' B2' : ℝ,
      Sys431 m (Real.log (a 0)) (Real.log (a 1)) θ1 θ2 A1' A2' B1' B2' →
        A1' = A1 ∧ A2' = A2 ∧ B1' = B1 ∧ B2' = B2)
    (x : ℝ) (hx : 0 < x) (i : Fin 2) :
    ∃ μ : Measure (ℝ × Fin 2), HasLimitLaw m P S x i (barrier m S a x) μ ∧
      (∀ y : ℝ, 0 < y → ∀ j : Fin 2,
        μ (Iic y ×ˢ {j}) = ENNReal.ofReal
          (PiCDF m (Real.log (a 0)) (Real.log (a 1)) θ1 θ2 A1 A2 B1 B2 (Real.log y) j)) ∧
      (∀ j : Fin 2, μ (Iic 0 ×ˢ {j}) = 0) := by sorry

end MFIrrev.Equilibrium
