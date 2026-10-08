-- Prove2me | Theorems.Thm_Katyusha_NonSC_eq_C4
-- name    : Katyusha.NonSC.eq_C4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T06:58:24.437588+00:00
-- url     : https://prove2.me/theorems/39cd3542-c84d-45a2-96ee-829b26d2c834
-- title:
--   Inequality (C.4) — the telescoped bound after $S$ epochs of Katyusha$^{\mathrm{ns}}$
-- statement:
--   Assume Problem (1.1) with each $f_i$ convex and $L$-smooth ($L>0$), $\psi$ convex, $n\ge1$, and $x^*$ a minimizer of $F=f+\psi$. Run Algorithm 2, $\mathtt{Katyusha}^{\mathrm{ns}}(x_0,S,L)$ with Option I and epoch length $m\ge1$, for $S\ge1$ epochs, so that $y_0=z_0=\widetilde x^0=x_0$. With $D_k=F(y_k)-F(x^*)$, $\widetilde D^0=F(\widetilde x^0)-F(x^*)$, $\tau_{1,s}=\frac2{s+4}$, $\tau_2=\frac12$, and $\mathbb E$ the expectation over all $Sm$ independent uniform indices,
--   $$\mathbb E\Big[\frac1{\tau_{1,S-1}^2}D_{Sm}+\frac{\tau_{1,S-1}+\tau_2}{\tau_{1,S-1}^2}\sum_{j=1}^{m-1}D_{(S-1)m+j}+\frac{3L}2\|z_{Sm}-x^*\|^2\Big]\le\frac{1-\tau_{1,0}-\tau_2}{\tau_{1,0}^2}D_0+\frac{\tau_2 m}{\tau_{1,0}^2}\widetilde D^0+\frac{3L}2\|z_0-x^*\|^2.$$
--
--   Since $\widetilde x^S$ is the average of $y_{(S-1)m+1},\dots,y_{Sm}$, this bound controls $F(\widetilde x^S)-F(x^*)$ and gives Theorem 4.1.
--
--   **Formalization Note** The paper's display writes $\|z_{Sm}-z^*\|^2$, a typo for $\|z_{Sm}-x^*\|^2$; the statement uses $x^*$. Since $y_0=\widetilde x^0=z_0=x_0$, the right-hand side is written with $x_0$ in all three places.
-- source:
--   Allen-Zhu, Katyusha: The First Direct Acceleration of Stochastic Gradient Methods, arXiv:1603.05953v6, App. C.1, (C.4), p. 27

import Mathlib
import Definitions.Def_SAGA_Convex_finiteSum
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_SAGA_Convex_sagaRun
import Definitions.Def_Katyusha_NonSC_step
import Definitions.Def_Katyusha_NonSC_run

namespace Katyusha.NonSC

/-- Inequality (C.4) of Allen-Zhu, arXiv:1603.05953v6, App. C.1, p. 27: for `S ≥ 1` epochs of
`Katyusha^ns(x₀, S, L)` (Algorithm 2, Option I, epoch length `m`), with `D_k = F(y_k) - F(x*)`,
`E[1/τ_{1,S-1}² D_{Sm} + (τ_{1,S-1} + τ₂)/τ_{1,S-1}² ∑_{j=1}^{m-1} D_{(S-1)m+j} + 3L/2 ‖z_{Sm} - x*‖²]`
is at most `(1 - τ_{1,0} - τ₂)/τ_{1,0}² D₀ + τ₂ m/τ_{1,0}² D̃⁰ + 3L/2 ‖z₀ - x*‖²`, where
`y₀ = z₀ = x̃⁰ = x₀`. The expectation is over all `S m` independent uniform indices. -/
theorem eq_C4 {d n m : ℕ} (hn : 0 < n) (hm : 1 ≤ m)
    (f : Fin n → EuclideanSpace ℝ (Fin d) → ℝ)
    (f' : Fin n → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (ψ : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ) (hL : 0 < L)
    (hf_grad : ∀ i x, HasGradientAt (f i) (f' i x) x)
    (hf_conv : ∀ i, ConvexOn ℝ Set.univ (f i))
    (hf_smooth : ∀ i x y, ‖f' i x - f' i y‖ ≤ L * ‖x - y‖)
    (hψ : ConvexOn ℝ Set.univ ψ)
    (P : ℝ → EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d))
    (hP : ∀ γ : ℝ, 0 < γ → ∀ v, SAGA.Convex.IsProxPoint ψ γ v (P γ v))
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ x, obj f ψ xstar ≤ obj f ψ x)
    (x0 : EuclideanSpace ℝ (Fin d)) (S : ℕ) (hS : 1 ≤ S) :
    SAGA.Convex.expectIdx n (S * m) (fun js =>
        1 / tau1 (S - 1) ^ 2 * (obj f ψ (iterYZ f' P L x0 (blocks (S := S) (m := m) js) ⟨S - 1, by omega⟩ m).1 - obj f ψ xstar)
          + (tau1 (S - 1) + tau2) / tau1 (S - 1) ^ 2 *
            ∑ j ∈ Finset.Ico 1 m, (obj f ψ (iterYZ f' P L x0 (blocks (S := S) (m := m) js) ⟨S - 1, by omega⟩ j).1 - obj f ψ xstar)
          + 3 * L / 2 * ‖(iterYZ f' P L x0 (blocks (S := S) (m := m) js) ⟨S - 1, by omega⟩ m).2 - xstar‖ ^ 2)
      ≤ (1 - tau1 0 - tau2) / tau1 0 ^ 2 * (obj f ψ x0 - obj f ψ xstar)
        + tau2 * (m : ℝ) / tau1 0 ^ 2 * (obj f ψ x0 - obj f ψ xstar)
        + 3 * L / 2 * ‖x0 - xstar‖ ^ 2 := by sorry

end Katyusha.NonSC
